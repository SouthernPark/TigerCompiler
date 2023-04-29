structure A = Absyn
structure S = Symbol

structure FindEscape : sig val findEscape : A.exp -> unit
                        end =
struct
type depth = int
type escEnv = (depth * bool ref) S.table

fun traverseVar(env: escEnv, d: depth, s: A.var) : unit =
  let
    fun trvar(A.SimpleVar(id, pos)) = (case S.look(env, id) of SOME(depth, r) => if depth < d
                                                                                then r := true else ()
                                                            | NONE => ())
      | trvar(A.FieldVar(var, symbol, pos)) = trvar var
      | trvar(A.SubscriptVar(var, exp, pos)) = (trvar var; traverseExp(env, d, exp))
  in
    trvar s
  end
and traverseExp(env: escEnv, d: depth, s: A.exp) : unit =
  let
    fun trexp(A.NilExp) = ()
      | trexp(A.IntExp(int)) = ()
      | trexp(A.StringExp(string, pos)) = ()
      | trexp(A.VarExp(var)) = traverseVar(env, d, var)
      | trexp(A.OpExp{left, oper, right, pos}) = (trexp left; trexp right)
      | trexp(A.IfExp({test=test_exp, then'=then_exp, else'=NONE, pos=pos'})) =
                                                  (trexp test_exp; trexp then_exp)
      | trexp(A.IfExp({test=test_exp, then'=then_exp, else'=SOME(else_exp), pos=pos'})) =
                                                  (trexp test_exp; trexp then_exp; trexp else_exp)
      | trexp(A.RecordExp({fields, typ, pos})) = (map (fn (sym, exp, pos) => trexp exp) fields; ())
      | trexp(A.ArrayExp({typ, size, init, pos})) = (trexp size; trexp init)
      | trexp(A.AssignExp{var, exp, pos}) = (traverseVar(env, d, var); trexp exp)
      | trexp(A.CallExp{func=func_name, args=exp_lst, pos=pos'}) = (map (fn arg => trexp arg) exp_lst; ())
      | trexp(A.LetExp{decs,body,pos}) =
        let
          val env' = traverseDecs(env, d, decs)
        in
          traverseExp(env', d, body)
        end
      | trexp(A.SeqExp(explst)) = (map (fn(exp, pos) => trexp exp) explst; ())
      | trexp(A.ForExp{var, escape, lo, hi, body, pos}) =
        let
          val env' = S.enter(env, var, (d, escape))
        in
          trexp lo;
          trexp hi;
          traverseExp(env', d, body)
        end
      | trexp(A.WhileExp{test, body, pos}) = (trexp test; trexp body)
      | trexp(A.BreakExp(pos)) = ()
  in
    trexp s
  end
and traverseDecs(env: escEnv, d: depth, s: A.dec list) : escEnv =
  let
    fun trdec(A.VarDec{name, escape, typ, init, pos}, env) =
        let
          val env' = S.enter(env, name, (d, escape))
          val _ = traverseExp(env', d, init)
        in
          env'
        end
      | trdec(A.TypeDec(typedecs), env) = env
      | trdec(A.FunctionDec(fundecs), env) =
        let
          fun trfundec({name, params, result, body, pos}) =
            let
              fun enterenv({name, escape, typ, pos}, env) = S.enter(env, name, (d + 1, escape))
              val env' = foldl enterenv env params
            in
              traverseExp(env', d + 1, body)
            end
        in
          map trfundec fundecs;
          env
        end
  in
    foldl trdec env s
  end

fun findEscape(prog: A.exp) : unit = traverseExp(S.empty, 0, prog)
end
