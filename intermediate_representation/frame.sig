signature FRAME =
sig type frame
    type access
    val wordsize : int
    val newFrame : {name: Temp.label, formals: bool list} -> frame			 
    val name : frame -> Temp.label			    
    val formals : frame -> access list				  
    val allocLocal : frame -> bool -> access
    val externalCall : string * Tree.exp list -> Tree.exp
end
    
