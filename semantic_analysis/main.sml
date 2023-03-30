structure Main =
struct
fun compile filename =
    let
      val abs_tree = Parse.parse filename
      val () = FindEscape.findEscape(abs_tree)
    in
      Semant.transProg abs_tree
    end
fun print filename =
    let
      val abs_tree = Parse.parse filename
      val () = FindEscape.findEscape(abs_tree)
    in
      PrintAbsyn.print (TextIO.stdOut, abs_tree)
    end

end
