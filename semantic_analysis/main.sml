structure Main =
struct
fun compile filename = Semant.transProg (Parse.parse filename)
fun print filename = PrintAbsyn.print (TextIO.stdOut, Parse.parse filename)
end
