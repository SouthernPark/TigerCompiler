signature TRANSLATE =
sig
    type level
    type access (* not the same as Frame.access *)
    type exp

    val outermost : level
    val newLevel : {parent: level, name: Temp.label,formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level -> bool -> access
end


structure Translate : TRANSLATE =
struct

structure F = MipsFrame
structure T = Tree

datatype exp = Ex of T.exp
	  |Nx of T.stm
	  |Cx of Temp.label * Temp.label -> T.stm

datatype level = TOP | Level of {parent: level, frame:F.frame } * unit ref
type access = level * F.access
val outermost = TOP

fun newLevel {parent, name, formals} =
    Level({parent=parent, frame=F.newFrame({name=name, formals=true::formals})}, ref ())

(* semant use this func to get formals location in frame *)
fun formals TOP :access list = []
  | formals curLevel :access list = let val Level({parent,frame}, _) = curLevel
                           val formalsF: F.access list = F.formals(frame)
                       in
                         map (fn (formal) => (curLevel, formal)) formalsF
                       end

(* semant uses this func to add local variable in frame *)
fun allocLocal TOP isEscape = ((ErrorMsg.error 0 "cannot allocate variables in outermost level");(TOP, F.allocLocal(F.newFrame({formals = [], name = Temp.newlabel()}))(true)))
  | allocLocal curLevel isEscape =
    let val Level({parent=_, frame=frame'}, _) = curLevel in (curLevel, F.allocLocal(frame') isEscape) end

end

