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

fun seq [x] = x
  | seq (a::l) = T.SEQ(a, seq l)
  | seq [] = T.EXP(T.CONST 0)

(* unNx function *)
fun unNx (Ex e) = T.EXP e
  | unNx (Nx s) = s
  | unNx (Cx c) = let
                    val l = Temp.newlabel()
                  in
                    seq [c(l, l), T.LABEL l]
                  end

(* unEx function *)
fun unEx (Ex e) = e
  | unEx (Nx s) = T.ESEQ(s, T.CONST 0)
  | unEx (Cx c) = let
                    val r = Temp.newtemp()
                    val t = Temp.newlabel()
                    val f = Temp.newlabel()
                  in
                    T.ESEQ(seq [T.MOVE(T.TEMP r, T.CONST 1),
                                c(t, f),
                                T.LABEL f,
                                T.MOVE(T.TEMP r, T.CONST 0),
                                T.LABEL t],
                            T.TEMP r)
                  end

(* unCx function : treat 0 and 1 specially to have simple and efficient translations *)
fun unCx (Ex e) = (case e of T.CONST 0 => (fn (t, f) => T.JUMP(T.NAME f, [f]))
                           | T.CONST 1 => (fn (t, f) => T.JUMP(T.NAME t, [t]))
                           | e => (fn (t, f) => T.CJUMP (T.EQ, e, T.CONST 0, f, t)))
  | unCx (Nx s) = raise ErrorMsg.Error
  | unCx (Cx c) = c

(* if expression *)
fun transIF (testexp, thenexp, elseexp) =
  let
    val test' = unCx testexp
    val then' = unEx thenexp
    val else' = unEx elseexp
    val label_t = Temp.newlabel()
    val label_f = Temp.newlabel()
    val cond = test'(label_t, label_f)
    val ans = Temp.newtemp()
    val label_end = Temp.newlabel()
  in
    Ex(T.ESEQ(seq [cond,
                    T.LABEL label_t,
                    T.MOVE(T.TEMP ans, then'),
                    T.JUMP(T.NAME label_end, [label_end]),
                    T.LABEL label_f,
                    T.MOVE(T.TEMP ans, else'),
                    T.LABEL label_end],
                    T.TEMP ans))
  end



end

