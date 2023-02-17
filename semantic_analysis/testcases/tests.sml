use "../types.sml";
use "../table.sig";
use "../table.sml";
use "../symbol.sml";
use "test_framework.sml";


fun isSubTy (Types.IMPOSSIBILITY, _) = true
  | isSubTy (_, Types.UNIT) = true
  | isSubTy (Types.NIL, Types.RECORD(lst, unique)) = true
  | isSubTy (Types.INT, Types.INT) = true
  | isSubTy (Types.STRING, Types.STRING) = true
  | isSubTy (Types.NIL, Types.NIL) = true
  | isSubTy (Types.ARRAY(t1, ref1), Types.ARRAY(t2, ref2)) = (ref1 = ref2)
  | isSubTy (Types.RECORD(lst1, ref1), Types.RECORD(lst2, ref2)) = (ref1 = ref2)
  | isSubTy (t1, t2) = false

val r = Types.RECORD([], ref ())
val same_r = r
val r2 = Types.RECORD([], ref ())
val a = Types.ARRAY(Types.INT, ref())
val same_a = a
val a2 = Types.ARRAY(Types.INT, ref())

(* test Types.IMPOSSIBILITY is subtype of all types *)
val it = general_test(isSubTy, "isSubTy", [(Types.IMPOSSIBILITY, Types.IMPOSSIBILITY), (Types.IMPOSSIBILITY, Types.NIL), (Types.IMPOSSIBILITY, Types.INT), (Types.IMPOSSIBILITY, Types.STRING), (Types.IMPOSSIBILITY, r), (Types.IMPOSSIBILITY, a), (Types.IMPOSSIBILITY, Types.UNIT)], [true, true, true, true, true, true, true])

val it = general_test(isSubTy, "isSubTy", [(Types.NIL, Types.IMPOSSIBILITY), (Types.INT, Types.IMPOSSIBILITY), (Types.STRING, Types.IMPOSSIBILITY), (r, Types.IMPOSSIBILITY), (a, Types.IMPOSSIBILITY), (Types.UNIT, Types.IMPOSSIBILITY)], [false, false, false, false, false, false])

(* test all type is a sub_type of UNIT *)

val it = general_test(isSubTy, "isSubTy", [(Types.NIL, Types.UNIT), (Types.INT, Types.UNIT), (Types.STRING, Types.UNIT), (r, Types.UNIT), (a, Types.UNIT), (Types.UNIT, Types.UNIT)], [true, true, true, true, true, true])


(* test nil is subtype of record *)
val it = general_test(isSubTy, "isSubTy", [(Types.NIL, r), (Types.NIL, Types.NIL)], [true, true])


(* test int to int, string, record, array, nil *)
val it = general_test(isSubTy, "isSubTy", [(Types.INT, Types.INT), (Types.INT, Types.STRING), (Types.INT, r), (Types.INT, a), (Types.INT, Types.NIL)], [true, false, false, false, false])


(* test string to string, int, record, array, nil *)
val it = general_test(isSubTy, "isSubTy", [(Types.STRING, Types.STRING), (Types.STRING, Types.INT), (Types.STRING, r), (Types.STRING, a), (Types.STRING, Types.NIL)], [true, false, false, false, false])

(* test nil to nil, record, string, int ,array *)
val it = general_test(isSubTy, "isSubTy", [(Types.NIL, Types.NIL), (Types.NIL, r), (Types.NIL, Types.STRING), (Types.NIL, Types.INT), (Types.NIL, a)], [true, true, false, false, false])

(* test record to same record, diff record, string, int, array, nil *)
val it = general_test(isSubTy, "isSubTy", [(r, same_r), (r, r2), (r, Types.STRING), (r, Types.INT), (r, a)], [true, false, false, false, false])

(* test array to same array, diff array, string, int, nil *)
val it = general_test(isSubTy, "isSubTy", [(a, same_a), (a, a2), (a, Types.STRING), (a, Types.INT), (a, Types.NIL)], [true, false, false, false, false])


(* == tests for leastUpperBound === *)
fun leastUpperBound (t, Types.IMPOSSIBILITY) = t
  | leastUpperBound (Types.IMPOSSIBILITY, t) = t
  | leastUpperBound (Types.UNIT, t) = Types.UNIT
  | leastUpperBound (t, Types.UNIT) = Types.UNIT
  | leastUpperBound (Types.NIL, Types.RECORD(lst, ref1)) = Types.RECORD(lst, ref1)
  | leastUpperBound (Types.RECORD(lst, ref1), Types.NIL) = Types.RECORD(lst, ref1)
  | leastUpperBound (Types.INT, Types.INT) = Types.INT
  | leastUpperBound (Types.STRING, Types.STRING) = Types.STRING
  | leastUpperBound (Types.NIL, Types.NIL) = Types.NIL
  | leastUpperBound (Types.ARRAY(t1, ref1), Types.ARRAY(t2, ref2)) = if ref1 = ref2
                                                                     then Types.ARRAY(t1, ref1)
                                                                     else Types.UNIT
  | leastUpperBound (Types.RECORD(lst1, ref1), Types.RECORD(lst2, ref2)) = if ref1 = ref2
                                                                           then Types.RECORD(lst1, ref1)
                                                                           else Types.UNIT
  | leastUpperBound (t1, t2) = Types.UNIT






(* test Types.IMPOSSIBILITY is subtype of all types *)
val it = general_test(leastUpperBound, "leastUpperBound", [(Types.IMPOSSIBILITY, Types.IMPOSSIBILITY), (Types.IMPOSSIBILITY, Types.NIL), (Types.IMPOSSIBILITY, Types.INT), (Types.IMPOSSIBILITY, Types.STRING), (Types.IMPOSSIBILITY, r), (Types.IMPOSSIBILITY, a), (Types.IMPOSSIBILITY, Types.UNIT)], [Types.IMPOSSIBILITY, Types.NIL, Types.INT, Types.STRING, r, a, Types.UNIT])

val it = general_test(leastUpperBound, "leastUpperBound", [(Types.NIL, Types.IMPOSSIBILITY), (Types.INT, Types.IMPOSSIBILITY), (Types.STRING, Types.IMPOSSIBILITY), (r, Types.IMPOSSIBILITY), (a, Types.IMPOSSIBILITY), (Types.UNIT, Types.IMPOSSIBILITY)], [Types.NIL, Types.INT, Types.STRING, r, a, Types.UNIT])

(* test all type is a sub_type of UNIT *)

val it = general_test(leastUpperBound, "leastUpperBound", [(Types.NIL, Types.UNIT), (Types.INT, Types.UNIT), (Types.STRING, Types.UNIT), (r, Types.UNIT), (a, Types.UNIT), (Types.UNIT, Types.UNIT)], [Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])


(* test nil is subtype of record *)
val it = general_test(leastUpperBound, "leastUpperBound", [(Types.NIL, r), (Types.NIL, Types.NIL)], [r, Types.NIL])

(* test int to int, string, record, array, nil *)
val it = general_test(leastUpperBound, "leastUpperBound", [(Types.INT, Types.INT), (Types.INT, Types.STRING), (Types.INT, r), (Types.INT, a), (Types.INT, Types.NIL)], [Types.INT, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])


(* test string to string, int, record, array, nil *)
val it = general_test(leastUpperBound, "leastUpperBound", [(Types.STRING, Types.STRING), (Types.STRING, Types.INT), (Types.STRING, r), (Types.STRING, a), (Types.STRING, Types.NIL)], [Types.STRING, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])

(* test nil to nil, record, string, int ,array *)
val it = general_test(leastUpperBound, "leastUpperBound", [(Types.NIL, Types.NIL), (Types.NIL, r), (Types.NIL, Types.STRING), (Types.NIL, Types.INT), (Types.NIL, a)], [Types.NIL, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])

(* test record to same record, diff record, string, int, array, nil *)
val it = general_test(leastUpperBound, "leastUpperBound", [(r, same_r), (r, r2), (r, Types.STRING), (r, Types.INT), (r, a)], [r, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])

(* test array to same array, diff array, string, int, nil *)
val it = general_test(leastUpperBound, "leastUpperBound", [(a, same_a), (a, a2), (a, Types.STRING), (a, Types.INT), (a, Types.NIL)], [a, Types.UNIT, Types.UNIT, Types.UNIT, Types.UNIT])
