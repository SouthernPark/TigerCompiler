structure intKey: ORD_KEY=
struct
  type ord_key = int
  val compare = Int.compare
end

structure stringKey: ORD_KEY=
struct
  type ord_key = string
  val compare = String.compare
end

structure MakeGraph :
sig 
  val instrs2graph : Assem.instr list -> Flow.flowgraph * Assem.instr Flow.Graph.node list
end =
struct
  structure F = Flow
  structure LabelMap = SplayMapFn(stringKey)
  
  fun instrs2graph instrlist = 
    let
      (* add nodeid->instruction into graph *)
      val node_id = ref 0
      fun addNode (instruction, currgraph) =
        let
          val newgraph = F.Graph.addNode(currgraph, !node_id, instruction)
          val update = node_id := !node_id + 1
        in
          newgraph
        end 

      val graph_with_nodes = foldl addNode F.Graph.empty instrlist
      val nodes = F.Graph.nodes(graph_with_nodes)
      
      (* update fgraph.def use and ismove *)
      fun updateFlow (currnode, (def, use, ismove)) = 
        let
          val instruction = F.Graph.nodeInfo(currnode)
        in
          case instruction of Assem.OPER{assem, dst, src, jump} => 
                          (
                            F.NodeMap.insert(def, F.Graph.getNodeID(currnode), dst),
                            F.NodeMap.insert(use, F.Graph.getNodeID(currnode), src),
                            F.NodeMap.insert(ismove, F.Graph.getNodeID(currnode), false)
                          )
                      | Assem.LABEL{assem, lab} => 
                          (
                            F.NodeMap.insert(def, F.Graph.getNodeID(currnode), []),
                            F.NodeMap.insert(use, F.Graph.getNodeID(currnode), []),
                            F.NodeMap.insert(ismove, F.Graph.getNodeID(currnode), false)
                          )
                      | Assem.MOVE{assem, dst, src} =>
                          (
                            F.NodeMap.insert(def, F.Graph.getNodeID(currnode), [dst]),
                            F.NodeMap.insert(use, F.Graph.getNodeID(currnode), [src]),
                            F.NodeMap.insert(ismove, F.Graph.getNodeID(currnode), true)
                          )
        end

      val (def_map, use_map, ismove_map) = foldl updateFlow (F.NodeMap.empty, F.NodeMap.empty, F.NodeMap.empty) nodes
      
      (* store label_name->nodeid from Assem.LABEL instruction *)
      fun storeLabel (currnode, label_map) = 
        let
          val instruction = F.Graph.nodeInfo(currnode)
        in
          case instruction of Assem.LABEL{assem, lab} => LabelMap.insert(label_map, Symbol.name(lab), F.Graph.getNodeID(currnode))
                          | _ => label_map
        end

      val label_map = foldl storeLabel LabelMap.empty nodes

      val node_index = ref 0
      (* instruction number i to number i+1 *)
      fun addNormalEdges (index, graph) = if index + 1 >= List.length(instrlist) 
                                          then graph 
                                          else F.Graph.addEdge(graph, {from=index, to=index+1})
      (* instruction number i to the other instruction where the label is *)
      fun addJumpEdges (index, label_list, graph) = 
        let
          fun updateJump (curr_label, curr_graph) = case LabelMap.find(label_map, Symbol.name(curr_label)) 
                                                      of SOME(node_index) => F.Graph.addEdge(curr_graph, {from=index, to=node_index})
                                                      | NONE => curr_graph
        in
          foldl updateJump graph label_list
        end
      (* add edges between nodes *)
      fun addEdges (instruction, currgraph) = 
        let
          val update_graph = case instruction of Assem.OPER{assem, dst, src, jump} => (
                                                    case jump of NONE => addNormalEdges(!node_index, currgraph)
                                                                | SOME(label_list) => addJumpEdges(!node_index, label_list, currgraph)
                                                  )
                                              | Assem.LABEL{assem, lab} => addNormalEdges(!node_index, currgraph)
                                              | Assem.MOVE{assem, dst, src} => addNormalEdges(!node_index, currgraph)
          val update_index = node_index := !node_index + 1
        in
          update_graph
        end
      
      val complete_graph = foldl addEdges graph_with_nodes instrlist

    in
      (F.FGRAPH{control=complete_graph, 
                def=def_map,
                use=use_map,
				        ismove=ismove_map}, F.Graph.nodes(complete_graph))
    end

end