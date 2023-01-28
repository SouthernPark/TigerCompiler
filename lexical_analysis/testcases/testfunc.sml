structure Test =
struct

fun parse filename =
    let val file = TextIO.openIn filename
        fun get _ = TextIO.input file
        val lexer = Mlex.makeLexer get
        fun do_it lst =
            let
              val t = lexer()
              val lst = t :: lst
            in
              if substring(t,0,3)="EOF" then lst else do_it lst
            end

        val res = do_it []
    in
      TextIO.closeIn file;
      rev res
    end

fun lst_size [] = 0
  | lst_size (a::l) = 1 + lst_size l;

fun lexer_test(filename:string, exp_lst) =
    let val opt_lst = parse filename
        fun check([], []) = print("== The output tokens of "^ filename ^"matches with expected tokens  ==\n")
          | check(a::e_l, b::o_l) = if a = b then check(e_l, o_l)
                                    else print("** Output token: "^ a ^" in file "^ filename ^" does not match with epxected token: "^b ^" **\n")

    in
      if (lst_size opt_lst) <> (lst_size exp_lst)
      then print "output length doesn't match expected output length\n"
      else
        check(exp_lst, opt_lst)
    end
end

