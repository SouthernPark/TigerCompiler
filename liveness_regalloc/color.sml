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

(* return: nodeID to degree table *)
fun getDegreeList initial nodes = foldl (fn (node, t) => case Temp.Table.look (initial, IGraph.getNodeID node) of
                                                             SOME(_) => t
                                                           | NONE => Temp.Table.enter (t, IGraph.getNodeID node, List.length(IGraph.adj node))
                                        ) Temp.Table.empty nodes

fun getDegree (degree, node) = case Temp.Table.look (degree, node) of
                                   SOME(d) => d
                                 | NONE => (print ("We should always find the degree of a temp: " ^ valOf(Temp.Table.look(Frame.tempMap, node)) ^"\n"); raise ErrorMsg.Error)

fun setDegree (degree, node, newDegree) = Temp.Table.enter (degree, node, newDegree)

(* adjList: int to int_set map *)
fun getAdjList initial nodes = foldl (fn (node, m) => case Temp.Table.look(initial, IGraph.getNodeID node) of
                                                          SOME(_) => m
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
fun decrementDegree K initial (node, (degree, spillWorkList, newSimplifyWorkList)) =
    case Temp.Table.look(initial, node) of
        SOME(_) => ((if IntSet.member(spillWorkList, node) then print("=====") else ());(degree, spillWorkList, newSimplifyWorkList))
      | NONE => let val d = getDegree (degree, node)
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
(* fun simplify K degree adjList spillWorkList simplifyWorklist selectStack =
    IntSet.foldl (fn (simplifyNode, (degree, spillWorkList, newSimplifyWorklist, selectStack)) =>
                     let
                       val selectStack = Stack.push(selectStack, simplifyNode)
                       val (degree, spillWorkList, newSimplifyWorkList) = IntSet.foldl (decrementDegree K) (degree, spillWorkList, IntSet.empty) (Adjacent adjList selectStack simplifyNode)
                     in
                       (degree, spillWorkList, newSimplifyWorklist, selectStack)
                     end
                 ) (degree, spillWorkList, IntSet.empty, selectStack) simplifyWorklist *)

fun simplify K initial degree adjList spillWorkList simplifyWorklist selectStack =
    let
      fun help (simplifyNode, (curr_degree, curr_spill, curr_simplify, curr_stack)) =
        let
          val new_stack = Stack.push(curr_stack, simplifyNode)
          val neighbours = Adjacent adjList curr_stack simplifyNode
          val (new_degree, new_spill, new_simplify) = IntSet.foldl (decrementDegree K initial) (curr_degree, curr_spill, curr_simplify) neighbours
        in
          (new_degree, new_spill, new_simplify, new_stack)
        end
    in
      IntSet.foldl help (degree, spillWorkList, IntSet.empty, selectStack) simplifyWorklist
    end


fun selectSpill selectStack adjList spillWorkList simplifyWorkList =
    let
      (* we select the spill node with the max degree *)
      fun findMaxDegree spillWorkList = IntSet.foldl (fn (node, maxNode) =>
                                                         let
                                                           val degree = IntSet.numItems(Adjacent adjList selectStack node)
                                                           val maxDegree = IntSet.numItems(Adjacent adjList selectStack maxNode)
                                                         in
                                                           if degree > maxDegree then node else maxNode
                                                         end
                                                     ) (List.nth(IntSet.listItems spillWorkList, 0)) spillWorkList
      val m = findMaxDegree spillWorkList (* node we selected *)
    in
      (* add to simplify list, so simpilfy list will be responsible for decrement ajacent degree and push to select stack *)
      (IntSet.add(simplifyWorkList, m), IntSet.subtract(spillWorkList, m))
    end

fun assignColors adjList precolored kcolors selectStack =
    let
      val coloredNodes = IntSet.foldl (fn (n, s) => IntSet.add(s, n)) IntSet.empty precolored
      val colorTable = foldl (fn (n, m) => IntMap.insert(m, n, n)) IntMap.empty (IntSet.listItems precolored)
      fun while_loop (selectStack, coloredNodes, colorTable, spilledNodes) =
          if Stack.isEmpty selectStack then (coloredNodes, colorTable, spilledNodes)
          else excludeUsedColors (selectStack, coloredNodes, colorTable, spilledNodes)
      and excludeUsedColors (selectStack, coloredNodes, colorTable, spilledNodes) =
          let
            val nodeid = valOf(Stack.top selectStack)
            val selectStack = Stack.pop selectStack
            val ok_colors = kcolors
            val neighbours = IntMap.lookup (adjList, nodeid)

            fun exclude (curr_nodeid, okcolors) =
                if IntSet.member(coloredNodes, curr_nodeid)
                then IntSet.subtract(okcolors, valOf(IntMap.find(colorTable, curr_nodeid)))
                else okcolors

            val ok_colors = IntSet.foldl exclude ok_colors neighbours

            fun assign () = if IntSet.isEmpty ok_colors then (coloredNodes, colorTable, IntSet.add(spilledNodes, nodeid))
                            else (IntSet.add(coloredNodes, nodeid), IntMap.insert(colorTable, nodeid, List.nth(IntSet.listItems ok_colors, 0)), spilledNodes)
            val (coloredNodes, colorTable, spilledNodes) = assign ()
          in
            while_loop(selectStack, coloredNodes, colorTable, spilledNodes)
          end
    in
      while_loop(selectStack, coloredNodes, colorTable, IntSet.empty)
    end

fun zip ([], []) = []
  | zip ([], l) = []
  | zip (l, []) = []
  | zip ((a1::l1), (a2::l2)) = (a1, a2) :: zip(l1, l2)

fun main (Liveness.IGRAPH({graph, tnode, gtemp, moves}), initial)  =
    let
      (* data structures *)
      val nodes = IGraph.nodes graph (* node list, could use IGraph.getNodeID to get id *)
      val nodeSet = foldl (fn (node, s) => IntSet.add(s, IGraph.getNodeID node)) IntSet.empty nodes
      val degree = getDegreeList initial nodes (* nodeID to degree table *)
      val adjList = getAdjList initial nodes (* nodeID to nodeID set map *)
      val adjMatrix = getAdjMatrix nodes (* (nodeID, nodeID) set *)
      val initialTempSet = getInitialTemps initial nodes (* temps that are not precolored, not machine regs *)
      val precolored = IntSet.difference (nodeSet, initialTempSet) (* temps that are machine regs *)
      val kcolors = IntSet.fromList(Frame.kregs) (* available colors *)
      val K = IntSet.numItems(kcolors) (* set K to the size of kcolors *)
      val () = print ("K: " ^ Int.toString(K) ^ "\n")
      val selectStack = Stack.empty

      (* make worklist *)
      val (spillWorklist, simplifyWorklist) = makeWorkList K degree initialTempSet
      val initialTempSet = IntSet.empty (* after make worklist, all nodes here should be removed *)

      fun repeat (degree, adjList, simplifyWorklist, spillWorklist, selectStack) =
        if IntSet.numItems(simplifyWorklist) > 0 (* simplify *)
        then (
          let
            val (degree, spillWorklist, simplifyWorklist, selectStack) = simplify K initial degree adjList spillWorklist simplifyWorklist selectStack
          in
            repeat(degree, adjList, simplifyWorklist, spillWorklist, selectStack)
          end
        )
        else if IntSet.numItems(spillWorklist) > 0 (* select spill *)
        then (
          let
            val (simplifyWorklist, spillWorklist) = selectSpill selectStack adjList spillWorklist simplifyWorklist
          in
            repeat(degree, adjList, simplifyWorklist, spillWorklist, selectStack)
          end
        )
        else selectStack

      val selectStack = repeat (degree, adjList, simplifyWorklist, spillWorklist, selectStack)

      (*Transform output into the same format as Color.color's output*)
      val (coloredNodes, colorTable, spilledNodes) =  assignColors adjList precolored kcolors selectStack
      val () = print("total size: " ^ Int.toString(List.length(nodes)) ^ "\n")
      val () = print("colored size: " ^ Int.toString(IntSet.numItems(coloredNodes)) ^ "\n")
      (*val () = print ("spilledNodes size: " ^ Int.toString(IntSet.numItems(spilledNodes)) ^ "\n")
      fun printString(t) = print (Int.toString(t) ^ "\n")
      val () = List.app printString (IntSet.listItems spilledNodes)*)



      val coloredNodeLst = IntSet.listItems coloredNodes
      val coloredRegLst = map (fn (coloredNode) =>
                               valOf(Temp.Table.look(Frame.tempMap, IntMap.lookup(colorTable, coloredNode)))
                           ) coloredNodeLst
      val zips = zip((IntSet.listItems coloredNodes), coloredRegLst)
      val allocation = foldl (fn ((temp, color), t) => Temp.Table.enter(t, temp, color)) Temp.Table.empty zips
    in
      (allocation, IntSet.listItems spilledNodes)
    end


(*
initial: machine register to string coloring
registers: list of string coloring
*)
fun color {interference: Liveness.igraph,
           initial: allocation,
           spillCost: Graph.node -> int,
           registers: Frame.register list} = main (interference, initial)

end

