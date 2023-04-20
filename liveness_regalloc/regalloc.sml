signature REG_ALLOC =
sig
structure Frame : FRAME
type allocation = Frame.register Temp.Table.table
val alloc : Assem.instr list * Frame.frame -> Assem.instr list * allocation
end

structure Reg_Alloc : REG_ALLOC =
struct
structure Frame = MipsFrame
type allocation = Frame.register Temp.Table.table

fun flatmap f xs = List.concat(List.map f xs)

fun unzip [] l1 l2 = (l1, l2)
  | unzip ((a1,a2)::l) l1 l2 = unzip l (l1 @ a1) (l2 @ a2)


fun rewriteProgram [] instructions _ newTemps = (instructions, newTemps)
  | rewriteProgram (spillNodeID::restNodes) instructions frame (newTemps:allocation) =
    let
	val newFrameLocal = Frame.allocLocal frame true
	val memExp = Frame.exp newFrameLocal (Tree.TEMP Frame.FP)


        fun printAssem(Assem.OPER{assem, dst, src, jump}) = print (assem)
          | printAssem(Assem.LABEL{assem, lab}) = print assem
          | printAssem(Assem.MOVE{assem, dst, src}) = print assem


	fun genStoreIns temp = let val ans = (MipsGen.codegen frame) (Tree.MOVE(memExp,Tree.TEMP temp))
                                   val h = hd ans

                               in
                                 ans
                               end

	fun genLoadIns temp = let val ans = (MipsGen.codegen frame) (Tree.MOVE(Tree.TEMP temp, memExp))
                                  val h = hd ans

                              in
                                ans
                              end


	(*find def and use of spill nodes in the input insts*)
	(*insert store to memory after each dst use and insert load from memory before each src use of spill node*)
	fun findDefandUse (ins as Assem.OPER{assem=assem, dst=dstlist,src=srclist,jump=jump}) =
	    if List.exists (fn y => y = spillNodeID) dstlist
	    then (let val newtemp = Temp.newtemp()
                      val () = print ("1. regalloc new temp: " ^ Int.toString(newtemp) ^ "\n")
                      val newDstList = map (fn n => if n=spillNodeID then newtemp else n) dstlist
		  in  [([Assem.OPER{assem=assem, dst=newDstList,src=srclist,jump=jump}, hd (genStoreIns newtemp)],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else if List.exists (fn y => y = spillNodeID) srclist
	    then (let val newtemp = Temp.newtemp()
                      val () = if assem = "" then print("!!!!!\n") else ()
                      val () = print ("2. regalloc new temp: " ^ Int.toString(newtemp) ^ "\n")
                      val () = print ("2. assem: " ^ assem)
                      val newSrcList = map (fn n => if n=spillNodeID then newtemp else n) srclist
		  in [([hd (genLoadIns newtemp), Assem.OPER{assem=assem, dst=dstlist,src=newSrcList,jump=jump}],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else [([ins],[])]
	  | findDefandUse (ins as Assem.MOVE{assem=assem, dst=dst,src=src}) =
	    if dst = spillNodeID
	    then (let val newtemp = Temp.newtemp()
                      val () = print ("3. regalloc new temp: " ^ Int.toString(newtemp) ^ "\n")
		  in [([Assem.MOVE{assem=assem, dst=newtemp,src=src}, hd (genStoreIns newtemp)],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else if src = spillNodeID
	    then (let val newtemp = Temp.newtemp()
                      val () = print ("4. regalloc new temp: " ^ Int.toString(newtemp) ^ "\n")
		  in [([hd (genLoadIns newtemp), Assem.MOVE{assem=assem, dst=newtemp,src=newtemp}],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else [([ins], [])]
	  | findDefandUse ins = [([ins], [])]

	(*return a list of (ins, temp*color) *)
	val insTempList = flatmap findDefandUse instructions
	val (newIns, newTempList) =  unzip insTempList [] []

	(*TODO: Color.color should label newTemps as non precolored*)
	val newTemps' = foldl (fn ((temp, color),t) =>Temp.Table.enter(t, temp, color)) newTemps newTempList
	(*TODO: if spillNode is live at the beginning or at the end of func?*)
    in
	rewriteProgram restNodes newIns frame newTemps'
    end

(*colored nodes should have no conflict with temps allocated for spill nodes*)
(*when conflict happens, use the color in newTemp set *)
fun mergeFn(val1:'a, val2:'a) = val2

fun alloc (insts, frame) =
    let
	val (flowgraph as Flow.FGRAPH{control, def, use, ismove},nodelist) = MakeGraph.instrs2graph insts
	val ((igraph as Liveness.IGRAPH{graph, tnode, gtemp, moves}), lomapfunc) = Liveness.interferenceGraph flowgraph
	val (updateAlloc, spillList) = Color.color {interference=igraph, initial=Frame.tempMap, spillCost=(fn x =>1), registers=Frame.registers}

        fun printAssem(Assem.OPER{assem, dst, src, jump}) = print (assem)
          | printAssem(Assem.LABEL{assem, lab}) = print assem
          | printAssem(Assem.MOVE{assem, dst, src}) = print assem


	(*val nodeList = map tnode spillList*)
        val () = print ("spilledNodes size: " ^ Int.toString(List.length(spillList)) ^ "\n")
        fun printString(t) = print (Int.toString(t) ^ "\n")
        (*val () = List.app printString (spillList)*)

	(*rewrite program to insert instructions, return new insts and new temp set*)
        val () = print ("original ins ============================== \n")
        val () = app printAssem insts
        val () = print ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n")
	val (updateIns, newTemps) = rewriteProgram spillList insts frame Temp.Table.empty
        val () = print ("new ins ============================== \n")
        val () = app printAssem updateIns
        val () = print ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n")

	(*union colored nodes with new temps*)
	(* val newAlloc = IntBinaryMap.unionWith mergeFn (updateAlloc, newTemps) *)
    in
	if List.length(spillList) > 0 then (alloc(updateIns, frame))
	else (insts, updateAlloc)
    end
end



