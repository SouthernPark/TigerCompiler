signature TRANSLATE =
sig
  type level
  type access (* not the same as Frame.access *)
  (* type exp *) (* remove below datatype exp and TODO in structure *)
  datatype exp = Ex of Tree.exp
                |Nx of Tree.stm
                |Cx of Temp.label * Temp.label -> Tree.stm
                |TODO
  type frag

  val outermost : level
  val newLevel : {parent: level, name: Temp.label,formals: bool list} -> level
  val formals: level -> access list
  val allocLocal: level -> bool -> access
  val transNIL : unit -> exp
  val transINT : int -> exp
  val transBINOP : exp * exp * Absyn.oper -> exp
  val transIF : exp * exp * exp -> exp
  val transASSIGN : exp * exp -> exp
  val transLET : exp list * exp -> exp
  val transSEQ : exp list -> exp
  val transWHILE : exp * exp * Temp.label -> exp
  val transBREAK : Temp.label -> exp
  val transCall: exp list * level * level * Temp.label -> exp

(* val transSIMPLEVAR: access * level -> exp
   val transFIELDVAR: exp * int -> exp
   val transSUBSCRIPTVAR: exp * exp -> exp *)
  val procEntryExit : {level: level, body: exp} -> unit
  val getResult : unit -> frag list
end

structure Translate : TRANSLATE =
struct

structure F = MipsFrame
structure T = Tree
structure A = Absyn

datatype exp = Ex of T.exp
	      |Nx of T.stm
              |Cx of Temp.label * Temp.label -> T.stm
              |TODO


datatype level = TOP | Level of {parent: level, frame:F.frame } * unit ref
type access = level * F.access
type frag = F.frag
val fraglist = ref [] : frag list ref 
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

(* static links *)
(* fun followSL () *)

(* NIL exp *)
fun transNIL () = Ex(T.CONST 0)

(* int exp *)
fun transINT (x) = Ex(T.CONST x)

(* string exp *)
(* fun transSTRING (string) =  *)

(* math operators *)
fun transBINOP (left, right, oper) =
  let
    val left' = unEx left
    val right' = unEx right
    val oper' = case oper of A.PlusOp => T.PLUS
                           | A.MinusOp => T.MINUS
                           | A.TimesOp => T.MUL
                           | A.DivideOp => T.DIV
                           | _ => raise ErrorMsg.Error
  in
    Ex(T.BINOP(oper', left', right'))
  end

(* comparison operators *)
fun transRELOP (left, right, oper, ty) =
  let
    val left' = unEx left
    val right' = unEx right
    val oper' = case oper of A.EqOp => T.EQ
                           | A.NeqOp => T.NE
                           | A.LtOp => T.LT
                           | A.LeOp => T.LE
                           | A.GtOp => T.GT
                           | A.GeOp => T.GE
                           | _ => raise ErrorMsg.Error
    val string_oper = case oper of A.EqOp => "stringEqual"
                           | A.NeqOp => "stringNE"
                           | A.LtOp => "stringLT"
                           | A.LeOp => "stringLE"
                           | A.GtOp => "stringGT"
                           | A.GeOp => "stringGE"
                           | _ => raise ErrorMsg.Error
    val cond = Cx(fn(t, f) => T.CJUMP(oper', left', right', t, f))
  in
    case ty of Types.STRING => Ex(F.externalCall(string_oper, [left', right']))
             | _ => cond
  end

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

(* record exp *)
fun transRECORD (fields) =
  let
    val fields_len = List.length fields
    val ptr = Temp.newtemp()
    fun initField ([], stmlist, index) = stmlist
      | initField (curr_exp::l, stmlist, index) =
        let
          val statement = T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP ptr, T.CONST(F.wordsize * index))), unEx curr_exp)
        in
          initField (l, statement::stmlist, index + 1)
        end
  in
    Ex(T.ESEQ(seq (initField(fields, [], 0)), T.TEMP ptr))
  end

(* array exp *)
fun transARRAY (size, init) =
  let
    val size' = unEx size
    val init' = unEx init
    val total_size = T.BINOP(T.PLUS, size', T.CONST 1)
    val ptr = Temp.newtemp()
  in
    Ex(T.ESEQ(seq [T.MOVE(T.TEMP ptr, F.externalCall("initArray", [total_size, init'])),
                    T.MOVE(T.MEM(T.TEMP ptr), size'),
                    T.MOVE(T.TEMP ptr, T.BINOP(T.PLUS, T.TEMP ptr, T.CONST F.wordsize))],
                    T.TEMP ptr))
  end

(* assign exp *)
fun transASSIGN (var, exp) =
  let
    val var' = unEx var
    val exp' = unEx exp
  in
    Nx(T.MOVE(var', exp'))
  end

(* call exp *)

fun isEqualLevel (TOP, TOP) = true
  | isEqualLevel (TOP, _) = false
  | isEqualLevel (_, TOP) = false
  | isEqualLevel (Level(_, ref1), Level(_, ref2)) = (ref1 = ref2)

(* return tree exp to get static link in the frame *)
fun getSLFromFrame(access, fp_exp) = F.exp access fp_exp

fun transCall(arg_exps, callerLevel, calleeLevel, calleeLabel) =
    let
      fun findStaticLink(callerLevel:level, calleeLevel:level, fp:T.exp) =
          let val Level({parent=callerParent, frame=callerFrame}, _) = callerLevel
              val Level({parent=calleeParent, frame=calleeFrame}, _) = calleeLevel
          in
            (* caller and callee at same level, we pass caller's sl to callee *)
            if isEqualLevel(callerLevel, calleeLevel) then getSLFromFrame((hd (F.formals callerFrame)) ,fp)
            else
              (* caller has exactly one higher level than calle, then we pass caller's FP as sl *)
              if isEqualLevel(callerLevel, calleeParent) then fp
              (* caller has lower level then callee *)
              else let val deref_fp = getSLFromFrame((hd (F.formals callerFrame)) ,fp) in findStaticLink(callerLevel, calleeParent, deref_fp) end
          end
      val sl = findStaticLink(callerLevel, calleeLevel, T.TEMP(F.FP))
      val args_exps = map unEx arg_exps
    in
      Ex(T.CALL(T.NAME(calleeLabel), sl::args_exps))
    end

(* let exp *)
fun transLET (decs, body) =
  let
    val decs' = map unNx decs
    val body' = unEx body
  in
    case List.length decs' of 0 => Ex(body')
                            | _ => Ex(T.ESEQ(seq decs', body'))
  end

(* seq exp *)
fun transSEQ [] = Ex(T.CONST 0)
  | transSEQ [exp] = exp
  | transSEQ (exp::explst) = Ex(T.ESEQ(unNx exp, unEx(transSEQ explst)))

(* for exp *)
fun transFOR (lo, hi, body, label_end) =
  let
    val lo' = unEx lo
    val hi' = unEx hi
    val body' = unNx body
    val v = Temp.newtemp()
    val end_reg = Temp.newtemp()
    val label_1 = Temp.newlabel()
    val label_2 = Temp.newlabel()
  in
    Nx(seq [T.MOVE(T.TEMP v, lo'),
            T.MOVE(T.TEMP end_reg, hi'),
            T.CJUMP(T.LE, T.TEMP v, T.TEMP end_reg, label_2, label_end),
            T.LABEL label_1,
            T.MOVE(T.TEMP v, T.BINOP(T.PLUS, T.TEMP v, T.CONST 1)),
            T.LABEL label_2,
            body',
            T.CJUMP(T.LT, T.TEMP v, T.TEMP end_reg, label_1, label_end),
            T.LABEL label_end])
  end

(* while exp *)
fun transWHILE (test, body, label_end) =
  let
    val label_test = Temp.newlabel()
    val label_start = Temp.newlabel()
    val test' = unCx test
    val body' = unNx body
  in
    Nx(seq [T.JUMP(T.NAME label_test, [label_test]),
            T.LABEL label_start,
            body',
            T.LABEL label_test,
            test'(label_start, label_end),
            T.LABEL label_end])
  end

(* break exp *)
fun transBREAK (label_break) = Nx(T.JUMP(T.NAME label_break, [label_break]))

(* simple var *)
(* fun transSIMPLEVAR *)

(* field var of record *)
fun transFIELDVAR (record, index) = Ex(T.MEM(T.BINOP(T.PLUS, unEx record, T.CONST(F.wordsize * index))))

(* subscript var of array *)
fun transSUBSCRIPTVAR (array, index) =
  let
    val array' = unEx array
    val index' = unEx index
    val array_ptr = Temp.newtemp()
    val index_reg = Temp.newtemp()
    val label_error = Temp.newlabel()
    val label_continue = Temp.newlabel()
    val label_valid = Temp.newlabel()
  in
    Ex(T.ESEQ(seq [T.MOVE(T.TEMP array_ptr, array'),
                    T.MOVE(T.TEMP index_reg, index'),
                    T.CJUMP(T.LE, T.TEMP index_reg, T.CONST 0, label_error, label_continue),
                    T.LABEL label_continue,
                    T.CJUMP(T.GE, T.TEMP index_reg, T.MEM(T.BINOP(T.MINUS, T.TEMP array_ptr, T.CONST 1)), label_error, label_valid),
                    T.LABEL label_error,
                    T.EXP(F.externalCall("exit", [T.CONST 1])),
                    T.LABEL label_valid],
                    T.MEM(T.BINOP(T.PLUS, T.TEMP array_ptr, T.BINOP(T.MUL, T.TEMP index_reg, T.CONST F.wordsize)))))
  end

(* side effect of remembering a PROC fragment *)
fun procEntryExit ({level=TOP, body=_}) = (ErrorMsg.error 0 "procEntryExit for a function declared in outermost level "; ())
  | procEntryExit ({level=Level({parent, frame}, unique), body=body}) =
    let
      val body' = unEx body
    in
      fraglist := !fraglist @ [F.PROC{body=T.MOVE(T.TEMP F.RV, body'), frame=frame}]
    end

fun getResult () = !fraglist

end

