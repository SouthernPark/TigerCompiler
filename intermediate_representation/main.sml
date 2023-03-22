structure Main =
struct
fun compile filename = Semant.transProg (Parse.parse filename)
fun compilePrint filename = let val frag_lst = Semant.transProg (Parse.parse filename)
                            in
                              Printtree.printProg frag_lst
                            end
end
