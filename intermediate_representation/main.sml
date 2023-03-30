structure Main =
struct
fun compile filename =
    let
      val abs_tree = Parse.parse filename
      val () = FindEscape.findEscape(abs_tree)
    in
      Semant.transProg abs_tree
    end

fun compilePrint filename =
    let
      val abs_tree = Parse.parse filename
      val () = FindEscape.findEscape(abs_tree)
      val frag_lst = Semant.transProg abs_tree
    in
      Printtree.printProg frag_lst
    end
end
