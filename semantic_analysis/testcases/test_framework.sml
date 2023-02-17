(* could use the following to test sml functions *)

(*
f: function we are going to test
input_lst: the list of arguments for function f
exp_lst: the list of expected output
*)
fun general_test (f, f_name:string, input_lst, exp_lst) = case (f, input_lst, exp_lst) of
                                                              (f, [], []) => print ("\n == " ^ f_name ^ ": textcase passed == \n")
                                                            | (f, (x::lst1), (y::lst2)) => if f x <> y then
                                                                                             print ("\n ** "^ f_name ^": test case not passed ** \n")
                                                                                           else general_test (f, f_name, lst1, lst2)

(*
usage example:

val () = general_test (min, "min", [(1,2), (4,3), (~1, ~2)], [1, 3, ~2])
output: == min: textcase passed ==

val () = general_test (min, "min", [(1,2)], [2])
output: **test case not passed**

*)
