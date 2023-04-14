signature CODEGEN =
sig
  structure Frame : FRAME
  val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN =
struct
structure Frame = MipsFrame
structure A = Assem
structure T = Tree
structure S = Symbol
(*
munchExp: Tree.exp -> Temp.temp
munchStm: Tree.stm -> unit
*)

fun intToString (n:int) : string =
    let val str = Int.toString(n)
    in
      if String.sub(str, 0) = #"~" then "-" ^ String.extract(str, 1, SOME(size str - 1))
      else str
    end

(* TODO: below is a fake implementation of maximal munch *)
fun codegen (frame) (stm: Tree.stm) : Assem.instr list =
    let val ilist = ref (nil: A.instr list)
        fun emit x= ilist := x :: !ilist
        fun result(gen) = let val t = Temp.newtemp() in gen t; t end

        fun binopIns (oper) = case oper of T.PLUS => "add"
                                         | T.MINUS => "sub"
                                         | T.MUL => "mul"
                                         | T.DIV => "div"

        fun relopIns (oper) = case oper of T.EQ => "beq"
                                         | T.NE => "bne"
                                         | T.LT => "blt"
                                         | T.GT => "bgt"
                                         | T.LE => "ble"
                                         | T.GE => "bge"

        fun munchStm (T.SEQ(stm1, stm2)) = (munchStm stm1; munchStm stm2)
          | munchStm (T.EXP(e)) = (munchExp e; ())
          (* sw *)
          | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) = (* # of nodes 4 *)
            emit(A.OPER{
                    assem = "sw `s0, " ^ intToString(i) ^ "(`s1)\n",
                    src = [munchExp e2, munchExp e1],
                    dst = [], jump = NONE
                })
          | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) = (* # of nodes 4 *)
            emit(A.OPER{
                    assem = "sw `s0, " ^ intToString(i) ^ "(`s1)\n",
                    src = [munchExp e2, munchExp e1],
                    dst = [], jump = NONE
                })
          | munchStm(T.MOVE(T.MEM(T.CONST i), e2)) = (* # of nodes 3 *)
            emit(A.OPER{
                    assem = "sw `s0, " ^ intToString(i) ^ "($zero)\n",
                    src=[munchExp e2],
                    dst=[],jump=NONE
                })
          | munchStm (T.MOVE(T.MEM(e1), e2)) = (* # of nodes 2 *)
            emit(A.OPER{
                    assem = "sw `s0, 0(`s1) \n",
                    src = [munchExp e2, munchExp e1],
                    dst = [], jump = NONE
                })
          (* move const to reg *)
          | munchStm (T.MOVE(T.TEMP t, T.CONST i)) = (* # of nodes 1 *)
            emit(A.OPER{
                    assem = "li `d0, " ^ intToString(i) ^ "\n",
                    src = [],
                    dst = [t], jump = NONE
                })
          (* move reg to reg *)
          | munchStm (T.MOVE(T.TEMP t, e2)) = (* # of nodes 1 *)
            emit(A.MOVE{
                    assem = "move `d0, `s0\n",
                    src = munchExp e2,
                    dst = t
                })
          (* label *)
          | munchStm (T.LABEL lab) = emit(A.LABEL{assem= S.name lab ^  ":\n", lab=lab})
          (* cjump *)
          | munchStm (T.CJUMP(oper, e1, e2, label_ture, label_false)) =
            emit(A.OPER{
                    assem = relopIns oper ^ " `s0, `s1, " ^ S.name(label_ture) ^ "\n",
                    src = [munchExp e1, munchExp e2],
                    dst = [], jump = SOME([label_ture, label_false])
                })
          (* jump *)
          | munchStm (T.JUMP(e1, label_lst)) =
            emit(A.OPER{
                    assem = "j " ^ S.name(hd(label_lst)) ^ "\n",
                    src = [],
                    dst = [], jump = SOME(label_lst)
                })
        and result (gen) = let val t = Temp.newtemp() in gen t; t end
        and munchExp (T.ESEQ(stm, exp)) = (munchStm(stm); munchExp exp)
          (* lw *)
          | munchExp (T.MEM(T.BINOP(T.PLUS, T.CONST i, e2))) = (* # of nodes 3 *)
            result(fn r => emit(A.OPER{
                                   assem = "lw `d0, " ^ intToString(i) ^ "(`s0)\n",
                                   src = [munchExp e2], dst = [r], jump = NONE
                  }))
          | munchExp (T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) = (* # of nodes 3 *)
            result(fn r => emit(A.OPER{
                                   assem = "lw `d0, " ^ intToString(i) ^ "(`s0)\n",
                                   src = [munchExp e1], dst = [r], jump = NONE
                  }))
          (* addi *)
          | munchExp (T.BINOP(T.PLUS, T.TEMP t, T.CONST i)) = (* # of nodes 2 *)
            result(fn r => emit(A.OPER{
                                   assem = "addi `d0, `s0, " ^ intToString(i) ^ "\n",
                                   src = [t], dst = [r], jump = NONE
                  }))
          | munchExp (T.BINOP(T.PLUS, e1, T.CONST i)) = (* # of nodes 2 *)
            result(fn r => emit(A.OPER{
                                   assem = "addi `d0, `s0, " ^ intToString(i) ^ "\n",
                                   src = [munchExp e1], dst = [r], jump = NONE
                  }))
          | munchExp (T.BINOP(T.PLUS, T.CONST i, e2)) = (* # of nodes 2 *)
            result(fn r => emit(A.OPER{
                                   assem = "addi `d0, `s0, " ^ intToString(i) ^ "\n",
                                   src = [munchExp e2], dst = [r], jump = NONE
                  }))
          (* binop *)
          | munchExp (T.BINOP(oper, e1, e2)) = (* # of nodes 2 *)
            result(fn r => emit(A.OPER{
                                   assem = binopIns oper ^ " `d0, `s0, `s1\n",
                                   src = [munchExp e1, munchExp e2], dst = [r], jump = NONE
                  }))
          (* const *)
          | munchExp (T.CONST i) = (* # of nodes 1 *)
            result(fn r => emit(A.OPER{
                                   assem = "li `d0, " ^ intToString(i) ^ "\n",
                                   src = [], dst = [r], jump = NONE
                  }))
          (* lw *)
          | munchExp (T.MEM e1) = (* # of nodes 1 *)
            result(fn r => emit(A.OPER{
                                    assem = "lw `d0, 0(`s0)\n",
                                    src = [munchExp e1], dst = [r], jump = NONE
                  }))
          (* temp *)
          | munchExp (T.TEMP t) = t
          (* name *)
          | munchExp (T.NAME lab) =
            result(fn r => emit(A.OPER{
                                    assem = "la `d0, " ^ Symbol.name(lab) ^ "\n",
                                    src = [], dst = [r], jump = NONE
                  }))
          (* call *)
          | munchExp (T.CALL(T.NAME callee_label, args)) =
            let
              val fp = T.TEMP Frame.SP (* new fp for the frame *)
              val extra_arg_num = List.length args - 4
              val offset = if extra_arg_num <= 0 then 0 else extra_arg_num * 4
              val new_sp_stm = T.MOVE(T.TEMP Frame.SP, T.BINOP(T.PLUS, fp, T.CONST offset))
              val old_sp_stm = T.MOVE(T.TEMP Frame.SP, fp)
            in
              (
                munchStm new_sp_stm; (* new sp *)
                emit(A.OPER{
                            assem = "jal " ^ Symbol.name(callee_label) ^ "\n",
                            src = munchArgs(0, args),
                            dst = Frame.return_address @ Frame.return_values @ Frame.callersaves_reg @ Frame.args_reg,
                            jump = NONE
                    }); (* why dst ? the sub-rountine may use and change these registers *)
                munchStm old_sp_stm; (* restore sp *)
                Frame.V0 (* return value *)
              )
            end
        and munchArgs (index, []) = []
          | munchArgs (index, curr_arg::args) =
            let
              val move_arg_stm = T.MOVE(T.TEMP(List.nth(Frame.args_reg, index)), curr_arg)
              val arg_temp = T.TEMP((List.nth(Frame.args_reg, index)))
              val move_sp_stm = T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP(Frame.SP), T.CONST(((index - 3) * 4)))), curr_arg)
            in
              if index < 4
              (* use a0-a4 regs *)
              then (munchStm(move_arg_stm); [munchExp arg_temp] @ munchArgs(index + 1, args))
              (* extra on stack *)
              else (munchStm(move_sp_stm); munchArgs(index + 1, args))
            end
    in
      munchStm stm;
      rev(!ilist)
    end
end



