signature FRAME =
sig type frame
    datatype access = InFrame of int | InReg of Temp.temp
    val FP: Temp.temp (* frame pointer register to hold current frame pointer *)
    val exp: access -> Tree.exp -> Tree.exp (* access -> FP -> var location *)

    datatype frag = PROC of {body : Tree.stm, frame : frame}
             |  STRING of Temp.label * string
    val SP : Temp.temp
    val V0 : Temp.temp
    val callersaves_reg : Temp.temp list
    val args_reg : Temp.temp list
    val return_address : Temp.temp list
    val return_values : Temp.temp list

    val wordsize : int
    val newFrame : {name: Temp.label, formals: bool list} -> frame
    val name : frame -> string
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val externalCall : string * Tree.exp list -> Tree.exp
    (* output of string is used in data segment assembly, diff ISA has diff def, that's why we put it here *)
    val string : Temp.label * string -> string
    val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
    val procEntryExit3 : frame * Assem.instr list -> {prolog: string, body : Assem.instr list, epilog: string}
end

