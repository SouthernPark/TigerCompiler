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

  fun size ([]) = 0
    | size (a::l) = 1 + size(l)

  (* isSubTy(t1, t2) checks if t1 is a subtype of t2, same type is also regarded as sub_type *)
  fun isSubTy (T.IMPOSSIBILITY, _) = true
    | isSubTy (_, T.UNIT) = true
    | isSubTy (T.NIL, T.RECORD(lst, _)) = true
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


  fun checkInt({exp, ty}, pos) = if isSubTy(ty, T.INT) then () else error pos ((T.name ty) ^ " is not a subtype of INT")

  fun checkSameType({exp=exp1, ty=ty1},{exp=exp2, ty=ty2}, pos) =
      if (isSubTy(ty1, Types.INT) andalso isSubTy(ty2, Types.INT)) then ()
      else
        if (isSubTy(ty1, Types.STRING) andalso isSubTy(ty2, Types.STRING)) then ()
        else error pos "type cannot be compared with <=, >=, >, <"

  fun checkEqual({exp=exp1, ty=T.UNIT},{exp=exp2, ty=_}, pos) = error pos "unit type can not be compared"
    | checkEqual({exp=exp1, ty=_},{exp=exp2, ty=T.UNIT}, pos) = error pos "unit type can not be compared"
    | checkEqual({exp=exp1, ty=T.NIL},{exp=exp2, ty=NIL}, pos) = error pos "nil can not be compared with nil"
    | checkEqual({exp=exp1, ty=ty1},{exp=exp2, ty=ty2}, pos)  = if (isSubTy(ty1, ty2) orelse isSubTy(ty2, ty1))
                                                                then ()
                                                                else error pos ("Type: " ^ T.name(ty1) ^ " and " ^ T.name(ty2) ^ "can not be compared")

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
            let
              val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs)
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
                (error pos ("undefined variable " ^ S.name id); {exp=(), ty=T.INT}))
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
          (* var dec with type not specified *)
      let fun trdec(A.VarDec{name, escape, typ=NONE, init, pos}, {venv, tenv}) = (* var x := exp *)
              let val {exp, ty} = transExp(venv, tenv) init
              in
                (* var x := nil is not allowed *)
                case ty of T.NIL => (error pos "NIL can not assign to var whose type is not determined";
                                     {venv=S.enter(venv, name, E.VarEntry{ty=T.IMPOSSIBILITY}), tenv=tenv})
                         | _ => {venv=S.enter(venv, name, E.VarEntry{ty=ty}), tenv=tenv}
              end
            (* var dec with type specified *)
            | trdec(A.VarDec{name, escape, typ=SOME(symbol, pos1), init, pos=pos2}, {venv, tenv})  =
              let
                val {exp, ty} = transExp(venv, tenv) init
                val var_ty = transTy(tenv, A.NameTy(symbol, pos1))
              in
                if not (isSubTy(ty, var_ty)) then error pos2 (T.name(ty) ^ " is not a subtype of " ^ T.name(var_ty)) else ();
                {venv=S.enter(venv, name, E.VarEntry{ty=var_ty}), tenv=tenv}
              end
            (* typedecs *)
            | trdec(A.TypeDec(typedecs), {venv, tenv}) =
              let
                fun putHeaders(cur_tydec, tenv) = (* put all the headers in tenv -> tenv' *)
                    let val {name, ty, pos} = cur_tydec
                    in
                      case S.look(tenv, name) of SOME(T.NAME(namety, unique)) => (
                        error pos ("type " ^ S.name name ^ " is already defined before"); S.enter(tenv, name, T.NAME(name, ref NONE)))
                      | _ => S.enter(tenv, name, T.NAME(name, ref NONE)) 
                    end
                fun processBodies(cur_tydec, tenv) =  (* process all the bodies in tenv' *)
                    let val {name, ty, pos} = cur_tydec
                    in (* assignments to ref variables *)
                      case S.look(tenv, name) of SOME(T.NAME(namety, unique)) => (unique := SOME(transTy(tenv, ty)); tenv)
                                               | _ => (error pos ("Undefined type " ^ S.name name); tenv)
                    end
                fun detectIllegalCycles([], tenv, typelist) = ()
                  | detectIllegalCycles(cur_tydec::l, tenv, typelist) = (* detect illegal cycles in type declarations *)
                    let
                      val {name, ty, pos} = cur_tydec
                    in
                      case S.look(tenv, name) of SOME(T.NAME(namety, unique)) => (
                         case !unique of SOME(T.NAME(mutual_namety, mutual_unique)) => (
                            if List.exists (fn cur_ty => S.name cur_ty = S.name mutual_namety) typelist
                            then error pos ("There's a illegal cycle in type declaration. ")
                            else detectIllegalCycles(l, tenv, namety::typelist)
                          )
                          | _ => detectIllegalCycles(l, tenv, typelist)
                      )
                      | _ => (error pos ("Undefined type " ^ S.name name))
                    end
                val tenv' = foldl putHeaders tenv typedecs
                val complete_tenv = foldl processBodies tenv' typedecs
              in
                detectIllegalCycles(typedecs, complete_tenv, []);
                {venv=venv, tenv=complete_tenv}
              end
      in
        foldl trdec {venv=venv, tenv=tenv} decs
      end

  and transTy (tenv, ty) =
      case ty of A.NameTy(symbol, pos) =>
                 (case S.look(tenv, symbol) of SOME(name_ty) => name_ty
                                             | NONE => (error pos ("Undefined type " ^ S.name symbol); T.IMPOSSIBILITY))
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




