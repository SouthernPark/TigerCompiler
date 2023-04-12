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
structure IntMap = IntRedBlackMap

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

(* return: nodeID to degree table, does not contain degree for precolored nodes to save space *)
fun getDegreeList initial nodes = foldl (fn (node, t) => case Temp.Table.look (initial, IGraph.getNodeID node) of
                                                             SOME(_) => t (* precolored node *)
                                                           | NONE => Temp.Table.enter (t, IGraph.getNodeID node, List.length(IGraph.adj node))
                                        ) Temp.Table.empty nodes

fun getDegree (degree, node) = case Temp.Table.look (degree, node) of
                                   SOME(d) => d
                                 | NONE => (print "We should always find the degree of a temp\n";raise ErrorMsg.Error)

fun setDegree (degree, node, newDegree) = Temp.Table.enter (degree, node, newDegree)

(* adjList: int to int_set map, does not contain adjcent nodes for precolored nodes to save space *)
fun getAdjList initial nodes = foldl (fn (node, m) => case Temp.Table.look (initial, IGraph.getNodeID node) of
                                                          SOME(_) => m (* precolored nodes *)
                                                        | NONE => IntMap.insert (m, IGraph.getNodeID node, IntSet.fromList(IGraph.adj node))
                                     ) IntMap.empty nodes

(* both node1 -> node2, node2 -> node1 will be added into adj matrix *)
fun addAdjMatrix(node1, node2, s) = let val s = IntPairSet.add(s, (node1, node2)); val s = IntPairSet.add(s, (node2, node1)) in s end
(* both node1 -> node2, node2 -> node1 will be removed from adj matrix *)
fun substractAdjMatrix(node1, node2, s) = let val s = IntPairSet.subtract(s, (node1, node2)); val s = IntPairSet.subtract(s, (node2, node1)) in s end

fun getAdjMatrix nodes = foldl (fn (node1, s) => foldl (fn (node2, s) => addAdjMatrix(IGraph.getNodeID node1 , node2, s)) s (IGraph.adj node1)) IntPairSet.empty nodes

(* those are the temps except from the 32 reg temps *)
fun getInitialTemps initial nodes = foldl (fn (node ,s) => case Temp.Table.look (initial, IGraph.getNodeID node) of
                                                               NONE => IntSet.add(s, IGraph.getNodeID node)
                                                             | _ => s) IntSet.empty nodes

fun makeWorkList K degree initialTemps = IntSet.foldl (fn (node, (spillWorklist, simplifyWorklist))
                                                          => if getDegree(degree, node) >= K
                                                             then (IntSet.add(spillWorklist, node), simplifyWorklist)
                                                             else (spillWorklist, IntSet.add(simplifyWorklist, node))
                                                      ) (IntSet.empty, IntSet.empty) initialTemps

(* return new degree and  new simplifyWorklist after simplified *)
fun decrementDegree K (node, (degree, spillWorkList, newSimplifyWorkList)) =
    let val d = getDegree (degree, node)
        val degree = setDegree (degree, node, d - 1)
    in
      if d = K then (degree, IntSet.subtract(spillWorkList, node), IntSet.add(newSimplifyWorkList, node))
      else (degree, spillWorkList, newSimplifyWorkList)
    end

fun Adjacent adjList selectStack node = let val nodeAdjSet = IntMap.lookup(adjList, node)
                                            val selectStackSet = IntSet.fromList (Stack.listItems selectStack)
                                            val diff = IntSet.difference (nodeAdjSet, selectStackSet)
                                        in
                                          diff
                                        end

(* return new degree, new simplifyWorklist, new spillWorkList and select stack  after simplified *)
fun simplify K degree adjList spillWorkList simplifyWorklist selectStack =
    IntSet.foldl (fn (simplifyNode, (degree, spillWorkList, newSimplifyWorklist, selectStack)) =>
                     let
                       val selectStack = Stack.push(selectStack, simplifyNode)
                       val (degree, spillWorkList, newSimplifyWorkList) = IntSet.foldl (decrementDegree K) (degree, spillWorkList, IntSet.empty) (Adjacent adjList selectStack simplifyNode)
                     in
                       (degree, spillWorkList, newSimplifyWorklist, selectStack)
                     end
                 ) (degree, spillWorkList, IntSet.empty, selectStack) simplifyWorklist


fun color {interference: Liveness.igraph,
           initial: allocation,
           spillCost: Graph.node -> int,
           registers: Frame.register list} =
    let
      val Liveness.IGRAPH({graph, tnode, gtemp, moves}) = interference
      (* data structures *)
      val nodes = IGraph.nodes graph (* node list, could use IGraph.getNodeID to get id *)
      val nodeSet = foldl (fn (node, s) => IntSet.add(s, IGraph.getNodeID node)) IntSet.empty nodes
      val degree = getDegreeList initial nodes (* nodeID to degree table *)
      val adjList = getAdjList initial nodes (* nodeID to nodeID set map *)
      val adjMatrix = getAdjMatrix nodes (* (nodeID, nodeID) set *)
      val initialTempSet = getInitialTemps initial nodes (* temps that are not precolored, not machine regs *)
      val precolored = IntSet.difference (nodeSet, initialTempSet)
      val K = IntSet.numItems precolored (* set K to the precolored machine registers *)

      (* make worklist *)
      val (spillWorklist, simplifyWorklist) = makeWorkList K degree initialTempSet
      val initialTempSet = IntSet.empty (* after make worklist, all nodes here should be removed *)
    in
      (initial, [])
    end



end

