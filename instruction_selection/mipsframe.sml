structure MipsFrame : FRAME =
struct
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, formals : access list, numLocalVars : int ref, curOffSet : int ref}
datatype frag = PROC of {body : Tree.stm,  frame : frame}
              | STRING of Temp.label * string

(* mips registers *)
(* https://en.wikibooks.org/wiki/MIPS_Assembly/Register_File *)
(* always 0 *)
val ZERO = Temp.newtemp()
(* reserved for assembler *)
val AT = Temp.newtemp()
(* stores results *)
val V0 = Temp.newtemp()
val V1 = Temp.newtemp()
(* stores arguments *)
val A0 = Temp.newtemp()
val A1 = Temp.newtemp()
val A2 = Temp.newtemp()
val A3 = Temp.newtemp()
(* temporaries, not saved *)
val T0 = Temp.newtemp()
val T1 = Temp.newtemp()
val T2 = Temp.newtemp()
val T3 = Temp.newtemp()
val T4 = Temp.newtemp()
val T5 = Temp.newtemp()
val T6 = Temp.newtemp()
val T7 = Temp.newtemp()
val T8 = Temp.newtemp()
val T9 = Temp.newtemp()
(* contents saved for use later *)
val S0 = Temp.newtemp()
val S1 = Temp.newtemp()
val S2 = Temp.newtemp()
val S3 = Temp.newtemp()
val S4 = Temp.newtemp()
val S5 = Temp.newtemp()
val S6 = Temp.newtemp()
val S7 = Temp.newtemp()
(* reserved by operating systems *)
val K0 = Temp.newtemp()
val K1 = Temp.newtemp()
(* global pointer *)
val GP = Temp.newtemp()
(* stack pointer *)
val SP = Temp.newtemp()
(* frame pointer *)
val FP = Temp.newtemp()
(* return address *)
val RA = Temp.newtemp()
val RV = Temp.newtemp()

val calleesaves_reg = [S0, S1, S2, S3, S4, S5, S6, S7]

val wordsize = 4
val numArgRegisters = 4 (*MIPS has 4 registers for argument*)
fun name {name=name,formals= _,numLocalVars=_,curOffSet=_} = Symbol.name name
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

fun string(l:Temp.label, s:string) = Symbol.name(l) ^ ": .asciiz " ^ s

fun procEntryExit2(frame, body) = body @ [Assem.OPER{assem="", src =[ZERO,RA,SP] @ calleesaves_reg, dst=[], jump=SOME[]}]

fun procEntryExit3({name, formals, numLocalVars, curOffSet}, body) =
                                    {prolog = "PROCEDURE " ^ (Symbol.name name) ^ "\n",
                                        body = body,
                                        epilog = "END " ^ (Symbol.name name) ^ "\n"}

end

