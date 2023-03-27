signature FRAME =
sig type frame
    datatype access = InFrame of int | InReg of Temp.temp
    val FP: Temp.temp (* frame pointer register to hold current frame pointer *)
    val exp: access -> Tree.exp -> Tree.exp (* access -> FP -> var location *)

    datatype frag = PROC of {body : Tree.stm, frame : frame}
             |  STRING of Temp.label * string
    val RV : Temp.temp

    val wordsize : int
    val newFrame : {name: Temp.label, formals: bool list} -> frame
    val name : frame -> string
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val externalCall : string * Tree.exp list -> Tree.exp
    (* output of string is used in data segment assembly, diff ISA has diff def, that's why we put it here *)
    val string: Temp.label * string -> string
end

