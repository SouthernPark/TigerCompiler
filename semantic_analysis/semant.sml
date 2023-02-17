signature SEMANT =
sig
  val transProg: Absyn.exp -> unit
end

structure Semant :> SEMANT =
struct

structure A = Absyn
structure E = Env
structure S = Symbol
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

(*
transExp (venv * tenv) -> Absyn.exp -> expty
trexp: Absyn.exp -> expty
trvar: Absyn.var -> expty
 *)
fun transExp(venv, tenv) =
    let
      fun trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) = (* Plus op expression: e1 + e2 *)
          (checkInt(trexp left, pos); checkInt(trexp right, pos); {exp=(), ty=Types.INT})
        | trexp (A.LetExp{decs,body,pos}) = (* let expression *)
          let val {venv=venv', tenv=tenv'} = transDec(venv, tenv, decs) in transExp(venv', tenv') body end

      and trvar (A.SimpleVar(id,pos)) = (* check var binding exist : id *)
          checkSimpleVar(A.SimpleVar(id,pos), venv)

    in
      trexp
    end
and transDec(venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = (* var x := exp *)
    let val {exp, ty} = transExp(venv, tenv, init)
    in {tenv=tenv, venv=S.enter(venv, name, E.VarEntry{ty=ty})} end
(*
var x : type-id : = exp
TODO: finish the typ = SOME(symbol, pos), need to check typ equal
Also, initializing expressions of type NIL must be constrained by a RECORD type
 *)


fun transProg(exp) = ()

end


