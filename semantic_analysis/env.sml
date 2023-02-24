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
    let val funlist = [(Symbol.symbol("print"), FunEntry{formals=[Types.STRING], result=Types.UNIT}),
		       (Symbol.symbol("flush"), FunEntry{formals=[], result=Types.UNIT}),
		       (Symbol.symbol("getchar"),FunEntry{formals=[], result=Types.STRING}),
		       (Symbol.symbol("ord"), FunEntry{formals=[Types.STRING], result=Types.INT}),
		       (Symbol.symbol("chr"), FunEntry{formals=[Types.INT], result=Types.STRING}),
		       (Symbol.symbol("size"), FunEntry{formals=[Types.STRING], result=Types.INT}),
		       (Symbol.symbol("substring"), FunEntry{formals=[Types.STRING, Types.INT, Types.INT], result=Types.STRING}),
		       (Symbol.symbol("concat"), FunEntry{formals=[Types.STRING, Types.STRING], result=Types.STRING}),
		       (Symbol.symbol("not"), FunEntry{formals=[Types.INT], result=Types.INT}),
		      (Symbol.symbol("exit"), FunEntry{formals=[Types.INT], result=Types.UNIT})]
	fun loadPredFunc ((symbol, func), funcEnv) = Symbol.enter(funcEnv,symbol, func)								 
    in
      foldl loadPredFunc Symbol.empty funlist
    end

val base_tenv : ty Symbol.table = getBaseTypeEnv()
val base_venv : enventry Symbol.table = getBaseFuncEnv()
end


