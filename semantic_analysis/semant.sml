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
type tenv = Types.ty S.table
type expty = {exp: Translate.exp, ty: Types.ty}

val error = ErrorMsg.error (* open error defined in errormsg.sml *)

(* isSubTy(t1, t2) checks if t1 is a subtype of t2, same type is also regarded as sub_type *)
fun isSubTy (Types.IMPOSSIBILITY, _) = true
  | isSubTy (_, Types.UNIT) = true
  | isSubTy (Types.NIL, Types.RECORD(lst, unique)) = true
  | isSubTy (Types.INT, Types.INT) = true
  | isSubTy (Types.STRING, Types.STRING) = true
  | isSubTy (Types.NIL, Types.NIL) = true
  | isSubTy (Types.ARRAY(t1, ref1), Types.ARRAY(t2, ref2)) = (ref1 = ref2)
  | isSubTy (Types.RECORD(lst1, ref1), Types.RECORD(lst2, ref2)) = (ref1 = ref2)
  | isSubTy (t1, t2) = false

fun leastUpperBound (t, Types.IMPOSSIBILITY) = t
  | leastUpperBound (Types.IMPOSSIBILITY, t) = t
  | leastUpperBound (Types.UNIT, t) = Types.UNIT
  | leastUpperBound (t, Types.UNIT) = Types.UNIT
  | leastUpperBound (Types.NIL, Types.RECORD(lst, ref1)) = Types.RECORD(lst, ref1)
  | leastUpperBound (Types.RECORD(lst, ref1), Types.NIL) = Types.RECORD(lst, ref1)
  | leastUpperBound (Types.INT, Types.INT) = Types.INT
  | leastUpperBound (Types.STRING, Types.STRING) = Types.STRING
  | leastUpperBound (Types.NIL, Types.NIL) = Types.NIL
  | leastUpperBound (Types.ARRAY(t1, ref1), Types.ARRAY(t2, ref2)) = if ref1 = ref2
                                                                     then Types.ARRAY(t1, ref1)
                                                                     else Types.UNIT
  | leastUpperBound (Types.RECORD(lst1, ref1), Types.RECORD(lst2, ref2)) = if ref1 = ref2
                                                                           then Types.RECORD(lst1, ref1)
                                                                           else Types.UNIT
  | leastUpperBound (t1, t2) = Types.UNIT

(* skip past all the NAMES *)
fun actual_ty (Types.NAME(symbol, ref(SOME(t)))) = actual_ty  t
  | actual_ty other_ty = other_ty


fun checkInt({exp, ty}, pos) = if isSubTy(ty, Types.INT) then () else error pos "integer required"

fun checkSimpleVar(A.SimpleVar(id,pos), venv) = case S.look(venv,id) of
                                                    SOME(E.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
                                                  | SOME(E.FunEntry{formals, result}) =>
                                                    (error pos ("var " ^ (S.name id) ^ " should not be a func");
                                                    {exp=(), ty=Types.IMPOSSIBILITY})
                                                  | NONE =>
                                                    (error pos ("undefined variable" ^ S.name id); {exp=(), ty=Types.INT})

fun checkSameType({exp=exp1, ty=Types.INT},{exp=exp2, ty=Types.INT}, pos) = ()
  | checkSameType({exp=exp1, ty=Types.STRING},{exp=exp2,ty = Types.STRING}, pos) = ()
  | checkSameType({exp=exp1, ty=_}, {exp=exp2, ty=_}, pos) = error pos "type cannot be compared"

fun checkEqual({exp=exp1, ty=Types.NIL},{exp=exp2, ty=Types.NIL}, pos) = ()
  | checkEqual({exp=exp1, ty=Types.INT},{exp=exp2, ty=Types.INT}, pos) = ()
  | checkEqual({exp=exp1, ty=Types.STRING},{exp=exp2, ty=Types.STRING},pos) = ()
  | checkEqual({exp=exp1, ty=Types.NIL},{exp=exp2, ty=Types.RECORD(lst, ref1)}, pos) = ()
  | checkEqual({exp=exp1, ty=Types.RECORD(lst, ref1)},{exp=exp2, ty=Types.NIL}, pos) = ()
  | checkEqual({exp=exp1, ty=Types.RECORD(_, ref1)},{exp=exp2, ty=Types.RECORD(_, ref2)}, pos) =
    if ref1 = ref2 then () else error pos "record type mismatch"
  | checkEqual({exp=exp1, ty=Types.ARRAY(_, ref1)},{exp=exp2, ty=Types.ARRAY(_, ref2)}, pos) =
    if ref1 = ref2 then () else error pos "array type mismatch"
  | checkEqual({exp=exp1, ty=_}, {exp=exp2, ty=_}, pos) = error pos "eq/neq operation require same types"
											   

(*
transExp (venv * tenv) -> Absyn.exp -> expty
trexp: Absyn.exp -> expty
trvar: Absyn.var -> expty
 *)
fun transExp(venv, tenv) =
    let fun trexp (A.NilExp) = {exp=(), ty=Types.NIL}
	  | trexp (A.IntExp(int)) = {exp=(), ty=Types.INT}
	  | trexp (A.StringExp(string)) = {exp=(), ty=Types.STRING}
	  | trexp (A.VarExp(var)) = trvar var
           (* operators *)
	  | trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) = 
            (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.MinusOp, right, pos}) =
	    (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.TimesOp, right, pos}) =
	    (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.DivideOp, right, pos}) =
	    (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.GeOp, right, pos}) =
	    (checkSameType(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.GtOp, right, pos}) =
	    (checkSameType(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.LeOp, right, pos}) =
	    (checkSameType(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.LtOp, right, pos}) =
	    (checkSameType(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.EqOp, right, pos}) =
	    (checkEqual(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
	    (checkEqual(trexp left, trexp right, pos); {exp=(), ty=Types.INT})
	  (*boolean operator*)
		
	  (*Assign*)		
	  | trexp (A.AssignExp{var, exp, pos}) =
	    let val vartype = trvar var
		val exptype = trexp exp
	    in
		(*check if the type of exp is a subtype of var*)
		if (isSubTy(#ty(exptype), #ty(vartype))) then ({exp=(), ty=(#ty(vartype))})
		else (error pos "assignment type mismatch"; {exp=(), ty=Types.IMPOSSIBILITY} )
	    end
		
	   (* let expression *)
          | trexp (A.LetExp{decs,body,pos}) =
              let val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs)
	      in transExp(venv', tenv') body
	      end
	  | trexp (A.SeqExp(explst)) =
	    let fun checkExprLst [] = {exp=(), ty= Types.UNIT}
		  | checkExprLst [(exp, pos)] = trexp exp
		  | checkExprLst ((exp,pos)::l) = (trexp exp; checkExprLst l)
	    in
		checkExprLst explst
	    end				
		

      and trvar (A.SimpleVar(id,pos)) = (* check var binding exist : id *)
          checkSimpleVar(A.SimpleVar(id,pos), venv)

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
    
(*
var x : type-id : = exp
TODO: finish the typ = SOME(symbol, pos), need to check typ equal
Also, initializing expressions of type NIL must be constrained by a RECORD type
 *)
 (* | transDec(venv, tenv, ) =*)

fun transProg(exp:A.exp):unit = (transExp (E.base_venv, E.base_tenv)(exp);())

end



