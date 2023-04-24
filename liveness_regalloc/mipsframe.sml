structure MipsFrame : FRAME =
struct
type register = string
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

val calleesaves_reg = [S0, S1, S2, S3, S4, S5, S6, S7]
val callersaves_reg = [T0, T1, T2, T3, T4, T5, T6, T7, T8, T9]
val args_reg = [A0, A1, A2, A3]
val return_address = [RA]
val return_values = [V0, V1]

val registers = ["$zero", "$at", "$v0", "$v1", "$a0", "$a1", "$a2", "$a3", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9", "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$k0", "$k1", "$gp", "$sp", "$fp", "$ra"]

val allregs = [ZERO, AT] @ return_values @ args_reg @ callersaves_reg @ calleesaves_reg @ [K0, K1] @ [GP, SP, FP, RA]
fun debugAllRegisters () = (foldl (fn (t, _) => (print(Int.toString(t) ^ " "); 0)) 0 allregs; print("\n"))

(* registers that can be assigned to any temps *)
val kregs = return_values @ args_reg @ calleesaves_reg @ callersaves_reg

fun zip ([], []) = []
  | zip ([], l) = []
  | zip (l, []) = []
  | zip ((a1::l1), (a2::l2)) = (a1, a2) :: zip(l1, l2)

fun createTempMap () =
    let
      val temp_color = zip (allregs, registers)
    in
      foldl (fn ((temp, color), m) => Temp.Table.enter(m, temp, color)) Temp.Table.empty temp_color
    end

val tempMap = createTempMap ()

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
				    else (curInRegFormals := !curInRegFormals+1;InReg(List.nth(args_reg, !curInRegFormals)))
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

fun string(l:Temp.label, s:string) = Symbol.name(l) ^ ": .asciiz \"" ^ String.toCString(s) ^ "\"\n"

(* temporaries zero, return-address, stack-pointer, and all the
    callee-saves registers are still live at the end of the function *)

fun procEntryExit1(frame, body) = foldl (fn (callee_reg, ans_lst) =>
                                            let
                                              val newTemp = Temp.newtemp()
                                              fun genStoreIns ()  = Assem.MOVE{assem="move `d0, `s0\n",
                                                                               src = callee_reg,
                                                                               dst= newTemp }

                                              fun genLoadIns () = Assem.MOVE{assem="move `d0, `s0\n",
                                                                             src = newTemp,
                                                                             dst= callee_reg}


                                            in
                                              [genStoreIns ()] @ ans_lst @ [genLoadIns ()]
                                            end
                                        ) body calleesaves_reg



fun procEntryExit2(frame, body) = body @ [Assem.OPER{assem="", src =[ZERO,RA,SP] @ calleesaves_reg, dst=[], jump=SOME[]}]


(* procedure entry/exit sequences, adding jal labels *)
fun procEntryExit3({name, formals, numLocalVars, curOffSet}, body) =
                                    {prolog = (Symbol.name name) ^ ":\n", body = body, epilog = "jr $ra\n"}
                                    (* for testing *)
                                    (* {prolog = "PROCEDURE " ^ (Symbol.name name) ^ "\n",
                                        body = body,
                                        epilog = "END " ^ (Symbol.name name) ^ "\n"} *)

end

