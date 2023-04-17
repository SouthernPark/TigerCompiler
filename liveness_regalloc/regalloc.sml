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
  | unzip ((a1,a2)::l) l1 l2 = unzip l (a1 @ l1) (a2 @ l2)
    
			      
fun rewriteProgram [] instructions _ newTemps = (instructions, newTemps)
  | rewriteProgram (spillNodeID::restNodes) instructions frame (newTemps:allocation) =    
    let					   
	val newFrameLocal = Frame.allocLocal frame true					     
	val memExp = Frame.exp newFrameLocal (Tree.TEMP Frame.FP)		       
	fun genStoreIns temp = (MipsGen.codegen frame) (Tree.MOVE(memExp,Tree.TEMP temp))
	fun genLoadIns temp = (MipsGen.codegen frame) (Tree.MOVE(Tree.TEMP temp, memExp))

	(*find def and use of spill nodes in the input insts*)
	(*insert store to memory after each dst use and insert load from memory before each src use of spill node*)						      
	fun findDefandUse (ins as Assem.OPER{assem=_, dst=dstlist,src=srclist,jump=_}) =    
	    if List.exists (fn y => y = spillNodeID) dstlist			   
	    then (let val newtemp = Temp.newtemp()     					   
		  in  [([ins, hd (genStoreIns newtemp)],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else if List.exists (fn y => y = spillNodeID) srclist		
	    then (let val newtemp = Temp.newtemp()      				      
		  in [([hd (genLoadIns newtemp), ins],[(newtemp,"$t"^Int.toString(newtemp))])] end)
	    else [([ins],[])]
	  | findDefandUse (ins as Assem.MOVE{assem=_, dst=dst,src=src}) =	   
	    if dst = spillNodeID
	    then (let val newtemp = Temp.newtemp()	      				     
		  in [([ins, hd (genStoreIns newtemp)],[(newtemp,"$t"^Int.toString(newtemp))])] end)		     
	    else if src = spillNodeID
	    then (let val newtemp = Temp.newtemp()		      
		  in [([hd (genLoadIns newtemp), ins],[(newtemp,"$t"^Int.toString(newtemp))])] end)
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
		
	(*val nodeList = map tnode spillList*)
	(*rewrite program to insert instructions, return new insts and new temp set*)	 
	val (updateIns, newTemps) = rewriteProgram spillList insts frame Temp.Table.empty
	(*union colored nodes with new temps*)						   
	(* val newAlloc = IntBinaryMap.unionWith mergeFn (updateAlloc, newTemps) *)
    in
	if List.length(spillList) > 0 then (alloc(updateIns, frame))
	else (insts, updateAlloc)
    end
end
    

    
