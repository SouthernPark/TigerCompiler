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
        and result (gen) = let val t = Temp.newtemp() in gen t; t end
        and munchExp (exp) = ()
    in
      munchStm stm;
      rev(!ilist)
    end
end



