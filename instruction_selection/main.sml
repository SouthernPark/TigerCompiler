structure Main = struct

structure Tr = Translate
structure F = MipsFrame
structure G = MipsGen
(* structure R = RegAlloc *)

fun getsome (SOME x) = x

(* val it = fn : TextIO.outstream -> MipsFrame.frag -> unit *)
fun emitproc out (F.PROC{body,frame}) =
    let val _ = print ("emit " ^ F.name frame ^ "\n")
        (* val _ = Printtree.printtree(out,body); *)
	val stms = Canon.linearize body
        (* val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	val instrs =   List.concat(map (G.codegen frame) stms')
        val format0 = Assem.format(Temp.makestring)
        val add_live_regs_instrs = F.procEntryExit2(frame, instrs)
        val add_procedure = F.procEntryExit3(frame, add_live_regs_instrs)
        val final_instrs = #body(add_procedure)
        val prolog = #prolog(add_procedure)
        val epilog = #epilog(add_procedure)
    in
      (* TextIO.output(out, prolog); *)
      app (fn i => TextIO.output(out,format0 i)) final_instrs
      (* TextIO.output(out, epilog) *)
    end
  | emitproc out (F.STRING(lab,s)) = TextIO.output(out,F.string(lab,s))

fun withOpenFile fname f =
    let val out = TextIO.openOut fname
    in (f out before TextIO.closeOut out)
       handle e => (TextIO.closeOut out; raise e)
    end

fun compile filename =
    let val absyn = Parse.parse filename
        (* TODO: implement find escape, val frags = (FindEscape.prog absyn; Semant.transProg absyn) *)
        val set_escape = FindEscape.findEscape absyn
        val frags = Semant.transProg absyn
    in
      withOpenFile (filename ^ ".s")
	           (fn out => (app (emitproc out) frags))
    end

fun compilePrint filename = let val frag_lst = Semant.transProg (Parse.parse filename)
                            in
                              Printtree.printProg frag_lst
                            end

end



