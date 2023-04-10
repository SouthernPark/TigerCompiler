structure IGraph = Flow.Graph

structure Liveness:
sig
  datatype igraph = IGRAPH of {graph: Temp.temp IGraph.graph, 
                                tnode: Temp.temp -> Temp.temp IGraph.node,
                                gtemp: Temp.temp IGraph.node -> Temp.temp, 
                                moves: (Temp.temp IGraph.node * Temp.temp IGraph.node) list}
  val interferenceGraph : Flow.flowgraph -> igraph * (Temp.temp IGraph.node -> Temp.temp list)
  val show : TextIO.outstream * igraph -> unit
end =
struct
  datatype igraph = IGRAPH of {graph: Temp.temp IGraph.graph, 
                                tnode: Temp.temp -> Temp.temp IGraph.node,
                                gtemp: Temp.temp IGraph.node -> Temp.temp, 
                                moves: (Temp.temp IGraph.node * Temp.temp IGraph.node) list}
  structure LiveSet = SplaySetFn(intKey)
  structure LiveMap = SplayMapFn(intKey)

  (* takes a flowgraph and return an IGraph and 
        a table mapping each flowgraph node to the liveout set of temps *)
  fun interferenceGraph (Flow.FGRAPH{control, def, use, ismove}) = 
    let
      fun insertEmptySet (currnode, currmap) = 
        LiveMap.insert(currmap, IGraph.getNodeID(currnode), LiveSet.empty)
      (* initialize livein_map and liveout_map with nodeid -> livein_set or liveout_set *)
      val livein_map = foldl insertEmptySet LiveMap.empty (IGraph.nodes(control))
      val liveout_map = foldl insertEmptySet LiveMap.empty (IGraph.nodes(control))

      (* check if livein_set and liveout_set are same in two maps for each node,
          used in iterate to a least fixed point *)
      fun checkLeastFixedPoint (curr_limap, last_limap, curr_lomap, last_lomap, nodes) =
        let
          fun isSameSet (curr_node, is_same) = 
            let
              val curr_nodeid = IGraph.getNodeID(curr_node)
              val curr_li_set = LiveMap.find(curr_limap, curr_nodeid)
              val last_li_set = LiveMap.find(last_limap, curr_nodeid)
              val curr_lo_set = LiveMap.find(curr_lomap, curr_nodeid)
              val last_lo_set = LiveMap.find(last_lomap, curr_nodeid)
            in
              is_same andalso LiveSet.equal(valOf(curr_li_set), valOf(last_li_set)) 
                      andalso LiveSet.equal(valOf(curr_lo_set), valOf(last_lo_set)) 
            end
        in
          foldl isSameSet true nodes
        end 

      (* compute livemap 
          LO[B] = Union(s in successor of B) LI[s]
          LI[B] = (LO[B] - def[B]) Union use[B]
          and iterate to a least fixed point *)
      fun computeLiveness (livein, liveout, nodes) = 
        let
          val last_li = livein
          val last_lo = liveout
          fun updateLiveness (li_map, lo_map) = 
            let
              fun update (curr_node, (curr_li, curr_lo)) = 
                let
                  val curr_nodeid = IGraph.getNodeID(curr_node)
                  fun lo_f (succ_nodeid, curr_set) = case LiveMap.find(curr_li, succ_nodeid) 
                                                    of SOME(set) => LiveSet.union(curr_set, set)
                                                     | NONE => curr_set
                  val update_lo_set = IGraph.foldSuccs lo_f LiveSet.empty curr_node
                  val def_of_node = case Flow.NodeMap.find(def, curr_nodeid)
                                      of SOME(templist) => LiveSet.addList(LiveSet.empty, templist)
                                       | NONE => LiveSet.empty
                  val use_of_node = case Flow.NodeMap.find(use, curr_nodeid)
                                      of SOME(templist) => LiveSet.addList(LiveSet.empty, templist)
                                       | NONE => LiveSet.empty
                  val update_li_set = LiveSet.union(use_of_node, LiveSet.difference(update_lo_set, def_of_node))
                in
                  (LiveMap.insert(curr_li, curr_nodeid, update_li_set), 
                    LiveMap.insert(curr_lo, curr_nodeid, update_lo_set))
                end
            in
              foldr update (li_map, lo_map) nodes (* from the last instruction to first one *)
            end
          val (update_li, update_lo) = updateLiveness(livein, liveout)
        in
          if checkLeastFixedPoint (update_li, last_li, update_lo, last_lo, nodes)
          then (update_li, update_lo)
          else computeLiveness(update_li, update_lo, nodes)
        end

      val (complete_limap, complete_lomap) = computeLiveness(livein_map, liveout_map, IGraph.nodes(control))

      fun makeIgraph (livein, liveout) = 
        let
          (* get all the temps used *)
          fun getTempList (nodes) = 
            let
              fun addlist (curr_node, curr_list) = 
                let
                  val node_id = IGraph.getNodeID(curr_node)
                  val def_temps = case Flow.NodeMap.find(def, node_id) of SOME(temps) => temps
                                                                            | NONE => []
                  val use_temps = case Flow.NodeMap.find(use, node_id) of SOME(temps) => temps
                                                                            | NONE => []
                in
                  curr_list @ def_temps @ use_temps
                end
            in
              foldl addlist [] nodes
            end
          val templist = getTempList(IGraph.nodes(control))
          (* add all the temps as nodes *)
          fun addNode (curr_temp, curr_graph) = IGraph.addNode(curr_graph, curr_temp, curr_temp)
          val ig_with_nodes = foldl addNode IGraph.empty templist

          (* add edges between def of node and liveout of node *)
          fun addEdges (curr_node, curr_graph) = 
            let
              val node_id = IGraph.getNodeID(curr_node)
              val def_list = case Flow.NodeMap.find(def, node_id) of SOME(temps) => temps
                                                                            | NONE => []
              val use_list = case Flow.NodeMap.find(use, node_id) of SOME(temps) => temps
                                                                            | NONE => []
              val is_moveinstr = case Flow.NodeMap.find(ismove, node_id) of SOME(true) => true
                                                                            | _ => false
              val lo_set = case LiveMap.find(liveout, node_id) of SOME(set) => set
                                                                | NONE => LiveSet.empty
              fun addDefHelper (curr_def, curr_graph) = 
                let
                  fun addLOHelper (curr_lotemp, graph) = if is_moveinstr 
                                                          then (case use_list of [t] => (if t <> curr_lotemp
                                                                                        then IGraph.doubleEdge(graph, curr_def, curr_lotemp)
                                                                                        else curr_graph)
                                                                                | _ => IGraph.doubleEdge(graph, curr_def, curr_lotemp)
                                                                )
                                                          else IGraph.doubleEdge(graph, curr_def, curr_lotemp)
                in
                  LiveSet.foldl addLOHelper curr_graph lo_set
                end
            in
              foldl addDefHelper curr_graph def_list
            end
          val ig_with_edges = foldl addEdges ig_with_nodes (IGraph.nodes(control))

          (* a mapping from temp to ig node *)
          fun tnode temp = IGraph.getNode(ig_with_edges, temp)

          (* a mapping from ig node to temp *)
          fun gtemp node = IGraph.nodeInfo(node)

          (* generate moves (temp * temp) list *)
          fun addMove (curr_node, curr_moves) =
            let
              val node_id = IGraph.getNodeID(curr_node)
              val is_moveinstr = case Flow.NodeMap.find(ismove, node_id) of SOME(true) => true
                                                                            | _ => false
            in
              if is_moveinstr
              then 
                let
                  val def_temps = case Flow.NodeMap.find(def, node_id) of SOME([d]) => [d]
                                                                        | _ => []
                  val use_temps = case Flow.NodeMap.find(use, node_id) of SOME([s]) => [s]
                                                                        | _ => []
                in
                  case (def_temps, use_temps) of ([d],[s]) => curr_moves @ [(tnode d, tnode s)]
                                  | _ => curr_moves
                end
              else curr_moves
            end 
          val moves = foldl addMove [] (IGraph.nodes(control))

          (* a mapping from flow-graph node to liveout temps *)
          fun node2TempFun flowgraph_node = 
            let
              val node_id = IGraph.getNodeID(flowgraph_node)
            in
              case LiveMap.find(complete_lomap, node_id) of SOME(set) => LiveSet.listItems(set)
                                                          | NONE => []
            end
        in
          (IGRAPH{graph=ig_with_edges, tnode=tnode, gtemp=gtemp, moves=moves}, node2TempFun)
        end

    in
      makeIgraph(complete_limap, complete_lomap)
    end
  
  fun show (outstream, IGRAPH{graph, tnode, gtemp, moves}) = 
    let
      fun stringify (nodeid, data) = 
        "Nodeid " ^ Int.toString(nodeid) ^ " : temp " ^ Int.toString(data)
    in
      IGraph.printGraph stringify graph
    end
    
end