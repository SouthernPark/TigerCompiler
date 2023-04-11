signature COLOR =
sig
  structure Frame : FRAME
  type allocation = Frame.register Temp.Table.table
  val color: {interference: Liveness.igraph,
              initial: allocation,
              spillCost: Graph.node -> int,
              registers: Frame.register list} -> allocation * Temp.temp list
end


structure Color : COLOR =
struct
structure Frame = MipsFrame

(* structure used to represent adjacent list *)
structure Int2List = ListMapFn(struct
                                type ord_key = int
                                val compare = Int.compare
                                end)

(* structure used to represent ajacent matrix *)
structure IntPair =
struct
type ord_key = int * int
val compare = fn ((x1, y1), (x2, y2)) =>
                 case Int.compare(x1, x2) of
                     EQUAL => Int.compare(y1, y2)
                   | ord => ord
end

structure IntPairSet = RedBlackSetFn(IntPair)

structure IntSet = RedBlackSetFn(struct
                                  type ord_key = int
                                  val compare = Int.compare
                                  end)

type allocation = Frame.register Temp.Table.table

(* return: nodeID -> degree table *)
fun getDegreeList nodes = foldl (fn (node, t) => Temp.Table.enter (t, IGraph.getNodeID node, List.length(IGraph.adj node))) Temp.Table.empty nodes

fun getDegree (degree, node) = case Temp.Table.look (degree, node) of
                                   SOME(d) => d
                                 | NONE => (print "We should always find the degree of a temp\n";raise ErrorMsg.Error)


fun getAdjList nodes = foldl (fn (node, m) => Int2List.insert (m, IGraph.getNodeID node, IGraph.adj node)) Int2List.empty nodes

(* both node1 -> node2, node2 -> node1 will be added into adj matrix *)
fun addAdjMatrix(node1, node2, s) = let val s = IntPairSet.add(s, (node1, node2)); val s = IntPairSet.add(s, (node2, node1)) in s end
(* both node1 -> node2, node2 -> node1 will be removed from adj matrix *)
fun substractAdjMatrix(node1, node2, s) = let val s = IntPairSet.subtract(s, (node1, node2)); val s = IntPairSet.subtract(s, (node2, node1)) in s end

fun getAdjMatrix nodes = foldl (fn (node1, s) => foldl (fn (node2, s) => addAdjMatrix(IGraph.getNodeID node1 , node2, s)) s (IGraph.adj node1)) IntPairSet.empty nodes

(* those are the temps except from the 32 reg temps *)
fun getInitialTemps initial nodes = foldl (fn (node ,s) => case Temp.Table.look (initial, IGraph.getNodeID node) of
                                                               NONE => IntSet.add(s, IGraph.getNodeID node)
                                                             | _ => s) IntSet.empty nodes



fun color {interference: Liveness.igraph,
           initial: allocation,
           spillCost: Graph.node -> int,
           registers: Frame.register list} =
    let
      val Liveness.IGRAPH({graph, tnode, gtemp, moves}) = interference

      val nodes = IGraph.nodes graph (* node list, could use IGraph.getNodeID to get id *)
      val nodeSet = foldl (fn (node, s) => IntSet.add(s, IGraph.getNodeID node)) IntSet.empty nodes
      val degree = getDegreeList nodes (* nodeID to degree table *)
      val adjList = getAdjList nodes (* nodeID to nodeID list table *)
      val adjMatrix = getAdjMatrix nodes (* (nodeID, nodeID) set *)
      val initialTempSet = getInitialTemps initial nodes (* temps that are not precolored, not machine regs *)
      val precolored = IntSet.difference (nodeSet, initialTempSet)
    in
      (initial, [])
    end



end

