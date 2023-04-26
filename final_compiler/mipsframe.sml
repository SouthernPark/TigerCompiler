structure MipsFrame : FRAME =
struct
type register = string
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, formals : access list, numLocalVars : int ref, curOffSet : int ref, numOutPara : int ref}
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
fun name {name=name,formals= _,numLocalVars=_,curOffSet=_, numOutPara=_} = Symbol.name name
fun formals {name=_, formals=formals,numLocalVars=_, curOffSet=_, numOutPara=_} = formals
fun newFrame {name, formals} =
    let val curInRegFormals = ref 0
	val curInFrameFormals = ref 0
	fun allocateFormals true = (curInFrameFormals := !curInFrameFormals+1;InFrame((!curInFrameFormals-1)*wordsize))
	  | allocateFormals false = if !curInRegFormals > numArgRegisters
				    then allocateFormals true
				    else (curInRegFormals := !curInRegFormals+1;InReg(List.nth(args_reg, !curInRegFormals)))
    in
	{name = name, formals = (map allocateFormals formals), numLocalVars = ref 0, curOffSet = ref 0, numOutPara = ref 0}
    end

fun allocLocal {name, formals, numLocalVars, curOffSet, numOutPara} isEscape =
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

(*copied from translate.sml to avoid cyclic dependency*)
fun seq [x] = x
  | seq [s1, s2] = Tree.SEQ(s1,s2)
  | seq (a::l) = Tree.SEQ(a, seq l)
  | seq [] = Tree.EXP(Tree.CONST 0)

fun max (n1 : int, n2 : int) = if n1 > n2 then n1 else n2


fun procEntryExit1(frame : frame, body:Tree.stm) =
    let
      val {name=_, formals=_, numLocalVars=_, curOffSet=_, numOutPara=numOutPara} = frame

      fun maxOutParaStm (Tree.LABEL(_)) = 0
        | maxOutParaStm (Tree.SEQ(stm1, stm2)) = max(maxOutParaStm stm1, maxOutParaStm stm2)
        | maxOutParaStm (Tree.JUMP(exp, _)) = maxOutParaExp(exp)
        | maxOutParaStm (Tree.CJUMP(relop, exp1, exp2, l1, l2)) = max(maxOutParaExp exp1, maxOutParaExp exp2)
        | maxOutParaStm (Tree.MOVE(exp1, exp2)) = max(maxOutParaExp exp1, maxOutParaExp exp2)
        | maxOutParaStm (Tree.EXP(exp)) = maxOutParaExp exp
      and maxOutParaExp (Tree.BINOP(binop, exp1, exp2)) = max(maxOutParaExp exp1, maxOutParaExp exp2)
        | maxOutParaExp (Tree.MEM(exp)) = maxOutParaExp exp
        | maxOutParaExp (Tree.TEMP(_)) = 0
        | maxOutParaExp (Tree.ESEQ(stm, exp)) = max(maxOutParaStm stm, maxOutParaExp exp)
        | maxOutParaExp (Tree.NAME(_)) = 0
        | maxOutParaExp (Tree.CONST(_)) = 0
        | maxOutParaExp (Tree.CALL(exp, exp_lst)) = max(List.length exp_lst,
                                                        max(maxOutParaExp exp,
                                                            foldl (fn (e, m) => max(m, maxOutParaExp e)) 0 exp_lst)
                                                       )
      (* side effect *)
      val () = numOutPara := (maxOutParaStm body)

      val genStore_body_genLoad =  foldl (fn (callee_reg, ans_lst) =>
                                            let
                                              val newTemp = Temp.newtemp()
                                              fun genStoreIns ()  = Tree.MOVE((Tree.TEMP newTemp), Tree.TEMP callee_reg)
                                              fun genLoadIns () = Tree.MOVE(Tree.TEMP callee_reg, Tree.TEMP newTemp)
                                            in
                                              [genStoreIns ()] @ ans_lst @ [genLoadIns ()]
                                            end
                                           ) [body] calleesaves_reg
	fun moveArgRegs (offset, []) = []
	  | moveArgRegs (offset, ((acc:access)::l)) = if offset < 4
					then Tree.MOVE((exp acc (Tree.TEMP FP)), Tree.TEMP(List.nth(args_reg, offset))) :: moveArgRegs(offset+1,l)
					else case acc of
						 InFrame _ => moveArgRegs(offset+1, l)
					       | InReg temp =>  Tree.MOVE((exp acc (Tree.TEMP FP)), Tree.TEMP(List.nth(args_reg, offset))) :: moveArgRegs(offset+1, l)
    in
	seq(moveArgRegs(0, (formals frame)) @ genStore_body_genLoad)
    end


fun procEntryExit2(frame, body) = body @ [Assem.OPER{assem="", src =[ZERO,RA,SP] @ calleesaves_reg, dst=[], jump=SOME[]}]

(* procedure entry/exit sequences, adding jal labels *)
fun procEntryExit3({name, formals, numLocalVars, curOffSet, numOutPara}, body) =
    let
      (* frame size: old fp, local variables, ra, callee_saves, formals(at least 4: a0-a3) *)
      val framesize = (1 + abs(!curOffSet) + 1 + List.length(calleesaves_reg)
                          + (if !numOutPara > 4 then !numOutPara else 4)) * wordsize
      (* function label *)
      val label = Assem.LABEL{assem = Symbol.name(name) ^ ":\n", lab = name}
      (* save old fp, set new fp, set new sp *)
      val saveFP = Assem.OPER{assem = "sw `s0, -4(`s1)\n", src = [FP, SP], dst = [], jump = NONE}
      val setFP = Assem.MOVE{assem = "move `d0, `s0\n", src = SP, dst = FP}
      val setSP = Assem.OPER{assem="addi `d0, `s0, -" ^ Int.toString(framesize) ^ "\n", src = [SP], dst = [SP], jump = NONE}
      val prolog_stm = [label] @ [saveFP] @ [setFP] @ [setSP]
      (* restore sp, restore fp*)
      val restoreSP = Assem.MOVE{assem="move `d0, `s0\n", src = FP, dst = SP}
      val restoreFP = Assem.OPER{assem = "lw `d0, -4(`s0)\n", src = [FP], dst = [FP], jump = NONE}
      val jr = Assem.OPER{assem = "jr `d0\n", src = [], dst = [RA], jump = NONE}
      val epilog_stm = [restoreSP] @ [restoreFP] @ [jr]
      (* final body *)
      val body = prolog_stm @ body @ epilog_stm
    in
      {prolog = "", body = body, epilog = ""}
    end

end

