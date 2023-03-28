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

(* TODO: below is a fake implementation of maximal munch *)
fun codegen (frame) (stm: Tree.stm) : Assem.instr list =
    let val ilist = ref (nil: A.instr list)
        fun emit x= ilist := x :: !ilist
        fun result(gen) = let val t = Temp.newtemp() in gen t; t end
        fun munchStm (T.SEQ(stm1, stm2)) = (munchStm stm1; munchStm stm2)
          | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) = (* # of nodes 4 *)
            emit(A.OPER{
                    assem = "sw `s0, " ^ Int.toString(i) ^ "(`s1)\n",
                    src = [munchExp e2, munchExp e1],
                    dst = [], jump = NONE
                })
          | munchStm (T.MOVE(T.TEMP t, T.CONST i)) = (* # of nodes 1 *)
            emit(A.OPER{
                    assem = "li `d0, " ^ Int.toString(i) ^ "\n",
                    src = [],
                    dst = [t], jump = NONE
                })
          | munchStm (T.LABEL lab) = emit(A.LABEL{assem= S.name lab ^  ":\n", lab=lab})
          | munchStm (T.JUMP(e1, label_lst)) =
            emit(A.OPER{
                    assem = "j " ^ S.name(hd(label_lst)) ^ "\n",
                    src = [],
                    dst = [], jump = SOME(label_lst)
                })
        and result (gen) = let val t = Temp.newtemp() in gen t; t end
        and munchExp (T.ESEQ(stm, exp)) = (munchStm(stm); munchExp exp)
          | munchExp (T.TEMP t) = t
          | munchExp (T.BINOP(PLUS, T.TEMP t, T.CONST i)) = (* # of nodes 2 *)
            result(fn r => emit(A.OPER{
                                   assem = "addi `d0, `s0, " ^ Int.toString(i) ^ "\n",
                                   src = [t], dst = [r], jump = NONE
                  }))

          | munchExp (T.CONST i) = (* # of nodes 1 *)
            result(fn r => emit(A.OPER{
                                   assem = "li `d0, " ^ Int.toString(i) ^ "\n",
                                   src = [], dst = [r], jump = NONE
                  }))
    in
      munchStm stm;
      rev(!ilist)
    end
end



