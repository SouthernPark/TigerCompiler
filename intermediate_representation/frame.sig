signature FRAME =
sig type frame
    type access
    val FP: Temp.temp (* frame pointer register to hold current frame pointer *)
    val exp: access -> Tree.exp -> Tree.exp (* access -> FP -> var location *)
    val wordsize : int
    val newFrame : {name: Temp.label, formals: bool list} -> frame
    val name : frame -> Temp.label
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val externalCall : string * Tree.exp list -> Tree.exp
end

