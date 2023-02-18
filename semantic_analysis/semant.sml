signature SEMANT =
sig
  val transProg: Absyn.exp -> unit
end

structure Semant :> SEMANT =
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  type venv = Env.enventry S.table
  type tenv = T.ty S.table
  type expty = {exp: Translate.exp, ty: T.ty}

  val error = ErrorMsg.error (* open error defined in errormsg.sml *)

  (* isSubTy(t1, t2) checks if t1 is a subtype of t2, same type is also regarded as sub_type *)
  fun isSubTy (T.IMPOSSIBILITY, _) = true
    | isSubTy (_, T.UNIT) = true
    | isSubTy (T.NIL, T.RECORD(lst, unique)) = true
    | isSubTy (T.INT, T.INT) = true
    | isSubTy (T.STRING, T.STRING) = true
    | isSubTy (T.NIL, T.NIL) = true
    | isSubTy (T.ARRAY(t1, ref1), T.ARRAY(t2, ref2)) = (ref1 = ref2)
    | isSubTy (T.RECORD(lst1, ref1), T.RECORD(lst2, ref2)) = (ref1 = ref2)
    | isSubTy (t1, t2) = false

  fun leastUpperBound (t, T.IMPOSSIBILITY) = t
    | leastUpperBound (T.IMPOSSIBILITY, t) = t
    | leastUpperBound (T.UNIT, t) = T.UNIT
    | leastUpperBound (t, T.UNIT) = T.UNIT
    | leastUpperBound (T.NIL, T.RECORD(lst, ref1)) = T.RECORD(lst, ref1)
    | leastUpperBound (T.RECORD(lst, ref1), T.NIL) = T.RECORD(lst, ref1)
    | leastUpperBound (T.INT, T.INT) = T.INT
    | leastUpperBound (T.STRING, T.STRING) = T.STRING
    | leastUpperBound (T.NIL, T.NIL) = T.NIL
    | leastUpperBound (T.ARRAY(t1, ref1), T.ARRAY(t2, ref2)) = if ref1 = ref2
      then T.ARRAY(t1, ref1)
      else T.UNIT
    | leastUpperBound (T.RECORD(lst1, ref1), T.RECORD(lst2, ref2)) = if ref1 = ref2
      then T.RECORD(lst1, ref1)
      else T.UNIT
    | leastUpperBound (t1, t2) = T.UNIT

  (* skip past all the NAMES *)
  fun actual_ty (T.NAME(symbol, ref(SOME(t)))) = actual_ty  t
    | actual_ty other_ty = other_ty


  fun checkInt({exp, ty}, pos) = if isSubTy(ty, T.INT) then () else error pos "integer required"

  fun checkSameType({exp=exp1, ty=T.INT},{exp=exp2, ty=T.INT}, pos) = ()
    | checkSameType({exp=exp1, ty=T.STRING},{exp=exp2,ty = T.STRING}, pos) = ()
    | checkSameType({exp=exp1, ty=_}, {exp=exp2, ty=_}, pos) = error pos "type cannot be compared"

  fun checkEqual({exp=exp1, ty=T.NIL},{exp=exp2, ty=T.NIL}, pos) = ()
    | checkEqual({exp=exp1, ty=T.INT},{exp=exp2, ty=T.INT}, pos) = ()
    | checkEqual({exp=exp1, ty=T.STRING},{exp=exp2, ty=T.STRING},pos) = ()
    | checkEqual({exp=exp1, ty=T.NIL},{exp=exp2, ty=T.RECORD(lst, ref1)}, pos) = ()
    | checkEqual({exp=exp1, ty=T.RECORD(lst, ref1)},{exp=exp2, ty=T.NIL}, pos) = ()
    | checkEqual({exp=exp1, ty=T.RECORD(_, ref1)},{exp=exp2, ty=T.RECORD(_, ref2)}, pos) =
      if ref1 = ref2 then () else error pos "record type mismatch"
    | checkEqual({exp=exp1, ty=T.ARRAY(_, ref1)},{exp=exp2, ty=T.ARRAY(_, ref2)}, pos) =
      if ref1 = ref2 then () else error pos "array type mismatch"
    | checkEqual({exp=exp1, ty=_}, {exp=exp2, ty=_}, pos) = error pos "eq/neq operation require same T"
											   

  (*
transExp (venv * tenv) -> Absyn.exp -> expty
trexp: Absyn.exp -> expty
trvar: Absyn.var -> expty
 *)
  fun transExp(venv, tenv) =
      let fun trexp (A.NilExp) = {exp=(), ty=T.NIL}
          | trexp (A.IntExp(int)) = {exp=(), ty=T.INT}
          | trexp (A.StringExp(string)) = {exp=(), ty=T.STRING}
          | trexp (A.VarExp(var)) = trvar var
          (* operators *)
          | trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) = 
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.MinusOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.TimesOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.DivideOp, right, pos}) =
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.GeOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.GtOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.LeOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.LtOp, right, pos}) =
            (checkSameType(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.EqOp, right, pos}) =
            (checkEqual(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          | trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
            (checkEqual(trexp left, trexp right, pos); {exp=(), ty=T.INT})
          (*boolean operator*)
		
          (*Assign*)		
          | trexp (A.AssignExp{var, exp, pos}) =
            let val vartype = trvar var
              val exptype = trexp exp
            in
              (*check if the type of exp is a subtype of var*)
              if (isSubTy(#ty(exptype), #ty(vartype))) then ({exp=(), ty=(#ty(vartype))})
              else (error pos "assignment type mismatch"; {exp=(), ty=T.IMPOSSIBILITY} )
            end
		
          (* let expression *)
          | trexp (A.LetExp{decs,body,pos}) =
            let val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs)
            in transExp(venv', tenv') body
            end
          | trexp (A.SeqExp(explst)) =
            let fun checkExprLst [] = {exp=(), ty= T.UNIT}
                | checkExprLst [(exp, pos)] = trexp exp
                | checkExprLst ((exp,pos)::l) = (trexp exp; checkExprLst l)
            in
              checkExprLst explst
            end				
		

        and trvar (A.SimpleVar(id,pos)) = (* check var binding exist : id *)
            (case S.look(venv,id) of
                SOME(E.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
              | SOME(E.FunEntry{formals, result}) =>
                (error pos ("var " ^ (S.name id) ^ " should not be a func");
                  {exp=(), ty=T.IMPOSSIBILITY})
              | NONE =>
                (error pos ("undefined variable" ^ S.name id); {exp=(), ty=T.INT}))
          | trvar (A.FieldVar(v,sym,pos)) = (* check v.sym type *)
            let
              val v_ty = #ty (trvar v)
              fun getSymType([],sym,pos) = (error pos ("Symbol " ^ (S.name sym) ^ " wasn't found in the record"); {exp=(), ty=T.IMPOSSIBILITY})
                | getSymType((symbol, sym_ty)::l,sym,pos) = 
                  if S.name symbol = S.name sym 
                  then {exp=(), ty=actual_ty sym_ty}
                  else getSymType(l,sym,pos)
            in
              case v_ty of T.RECORD(fields_list,unique) => getSymType(fields_list,sym,pos)
              | _ => (error pos ("None record type cannot find a field"); {exp=(), ty=T.IMPOSSIBILITY})
            end
          | trvar (A.SubscriptVar(v,exp,pos)) = (* check v[exp] type *)
            let
              val v_ty = #ty (trvar v)
            in
              case v_ty of T.ARRAY(array_ty, _) => (checkInt(trexp exp,pos); {exp=(), ty=actual_ty array_ty})
              |  _ => (error pos ("None array type cannot be subscripted"); {exp=(), ty=T.IMPOSSIBILITY})
            end
      in
        trexp
      end
  and transDec (venv, tenv, []) = {venv = venv, tenv = tenv}
    | transDec (venv, tenv, decs) = 
      let fun trdec(A.VarDec{name, escape, typ=NONE, init, pos}, {venv, tenv}) = (* var x := exp *)
            let val {exp, ty} = transExp(venv, tenv) init
            in {venv=S.enter(venv, name, E.VarEntry{ty=ty}), tenv=tenv} end
      in
        foldl trdec {venv=venv, tenv=tenv} decs
      end
  and transTy (tenv, ty) =  
      case ty of A.NameTy(symbol, pos) => (
            case S.look(tenv, symbol) of SOME(name_ty) => name_ty
            | NONE => (error pos ("Undefined type " ^ S.name symbol); T.IMPOSSIBILITY)
          )
      | A.RecordTy(fields_list) => (
          let
            fun getFieldType(curr_field, result) = 
                let
                  val {name, escape, typ, pos} = curr_field
                in
                  case S.look(tenv, typ) of SOME(name_ty) => (name, name_ty)::result
                  | NONE => (error pos ("Undefined type " ^ S.name typ); (name, T.IMPOSSIBILITY)::result)
                end
            val results = foldr getFieldType [] fields_list
          in
            T.RECORD(results, ref ())
          end
        )
      | A.ArrayTy(symbol, pos) => (
          case S.look(tenv, symbol) of SOME(name_ty) => T.ARRAY(name_ty, ref ())
          | NONE => (error pos ("Undefined type " ^ S.name symbol); T.ARRAY(T.IMPOSSIBILITY, ref ()))
        )
  (*
var x : type-id : = exp
TODO: finish the typ = SOME(symbol, pos), need to check typ equal
Also, initializing expressions of type NIL must be constrained by a RECORD type
 *)
  (* | transDec(venv, tenv, ) =*)

  fun transProg(exp:A.exp):unit = (transExp (E.base_venv, E.base_tenv)(exp);())

end



