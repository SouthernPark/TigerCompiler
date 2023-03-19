structure MipsFrame : FRAME =
struct
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, formals : access list, numLocalVars : int ref, curOffSet : int ref}
val FP = Temp.newtemp()

datatype frag = PROC of {body : Tree.stm, frame : frame}
             |  STRING of Temp.label * string
val RV = Temp.newtemp()

val wordsize = 4
val numArgRegisters = 4 (*MIPS has 4 registers for argument*)
fun name {name=name,formals= _,numLocalVars=_,curOffSet=_} = name
fun formals {name=_, formals=formals,numLocalVars=_, curOffSet=_} = formals
fun newFrame {name, formals} =
    let val curInRegFormals = ref 0
	val curInFrameFormals = ref 0
	fun allocateFormals true = (curInFrameFormals := !curInFrameFormals+1;InFrame((!curInFrameFormals-1)*wordsize))
	  | allocateFormals false = if !curInRegFormals > numArgRegisters
				    then allocateFormals true
				    else (curInRegFormals := !curInRegFormals+1;InReg(Temp.newtemp()))
    in
	{name = name, formals = (map allocateFormals formals), numLocalVars = ref 0, curOffSet = ref 0 }
    end

fun allocLocal {name, formals, numLocalVars, curOffSet} isEscape =
    (numLocalVars := !numLocalVars + 1;
    case isEscape of
	true => (curOffSet := !curOffSet-wordsize; InFrame(!curOffSet))
     |  false => InReg(Temp.newtemp()))

fun externalCall (s, args) = Tree.CALL(Tree.NAME(Temp.namedlabel s), args)

(* given location and frame pointer exp, return expression to get content in that address/register *)
fun exp access fp_exp =
    case access of InReg(tmp) => Tree.TEMP tmp
                 | InFrame(offset) => Tree.MEM(Tree.BINOP(Tree.PLUS, fp_exp, Tree.CONST(offset)))

end

