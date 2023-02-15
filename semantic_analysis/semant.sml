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

(* skip past all the NAMES *)
fun actual_ty (Types.NAME(symbol, ref(SOME(t)))) = actual_ty  t
  | actual_ty other_ty = other_ty


fun checkInt({exp, ty}, pos) = case ty of Types.INT => ()
                                        | _ => error pos "integer required"

fun checkSimpleVar(A.SimpleVar(id,pos), venv) = case S.look(venv,id) of
                                                    SOME(E.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
                                                  | SOME(E.FunEntry{formals, result}) =>
                                                    (error pos ("var " ^ (S.name id) ^ " should not be a func");
                                                    {exp=(), ty=Types.INT})
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
  | transDec(venv, tenv, ) =

fun transProg(exp) = ()

end


