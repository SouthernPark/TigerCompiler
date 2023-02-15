signature ENV =
sig
  type access (* don't quite understand its use *)
  type ty
  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}

  val base_tenv : ty Symbol.table (* predefined types *)
  val base_venv : enventry Symbol.table (* predefined functions *)
end

structure Env :> ENV
where type ty = Types.ty=
struct
type access = unit ref
type ty = Types.ty
datatype enventry = VarEntry of {ty: ty}
                  | FunEntry of {formals: ty list, result: ty}
fun getBaseTypeEnv() =
    let val tenv = Symbol.empty
        val tenv = Symbol.enter(tenv, Symbol.symbol("int"), Types.INT)
        val tenv = Symbol.enter(tenv, Symbol.symbol("string"), Types.STRING)
    in
      tenv
    end

fun getBaseFuncEnv() =
    (* predefined functions are in appendix A like: flush, ord, chr, size *)
    let val venv = Symbol.empty
    in
      venv
    end

val base_tenv : ty Symbol.table = getBaseTypeEnv()
val base_venv : enventry Symbol.table = getBaseFuncEnv()
end


