CM.make "../../sources.cm";
use "../testfunc.sml";

Test.lexer_test("ql143_test1.tig", ["TIMES   16","DIVIDE   17","TIMES   40","ID(abc)     42","TIMES   46","DIVIDE   47","ID(def)     49","TIMES   53","DIVIDE   54","EOF   56"]);

Test.lexer_test("ql143_test2.tig",["LET   44","TYPE   49","ID(arrtype)     55","EQ   63","ARRAY   65",
                                   "OF   71","ID(int)     74","VAR   79","ID(arr1)     83","COLON   87",
                                   "ID(arrtype)     88","ASSIGN   96","ID(arrtype)     99","LBRACK   107",
                                   "INT(10)   108","RBRACK   110", "OF   112", "INT(0)   115", "IN   117",
                                   "ID(arr1)     121", "END   126", "EOF   129"])


