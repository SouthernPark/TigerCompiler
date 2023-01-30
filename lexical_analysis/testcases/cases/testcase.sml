CM.make "../../sources.cm";
use "../testfunc.sml";


(* cases that will report error *)
Test.lexer_test("ys322_test1.tig", ["ID(string)     2","ID(s1)     9","ASSIGN   12",
                                    "STRING(xxx\nxxxyz)     15","SEMICOLON   33","ID(string)     61",
                                    "ID(s2)     68","ASSIGN   71","EOF   60"]);

Test.lexer_test("ql143_test11.tig", ["EOF   50"]);

Test.lexer_test("ql143_test12.tig", ["EOF   12"]);

Test.lexer_test("ql143_test13.tig", ["EOF   10"]);

print "\n-------no error should occur in the following--------\n\n";

(* cases that will not report error *)

Test.lexer_test("ql143_test1.tig", ["TIMES   16","DIVIDE   17","TIMES   40","ID(abc)     42","TIMES   46","DIVIDE   47","ID(def)     49","TIMES   53","DIVIDE   54","EOF   56"]);

Test.lexer_test("ql143_test2.tig",["LET   44","TYPE   49","ID(arrtype)     55","EQ   63","ARRAY   65",
                                   "OF   71","ID(int)     74","VAR   79","ID(arr1)     83","COLON   87",
                                   "ID(arrtype)     88","ASSIGN   96","ID(arrtype)     99","LBRACK   107",
                                   "INT(10)   108","RBRACK   110", "OF   112", "INT(0)   115", "IN   117",
                                   "ID(arr1)     121", "END   126", "EOF   129"]);


Test.lexer_test("ql143_test3.tig", ["VAR   2","ID(str)     6","ASSIGN   10","STRING(normal string)     13",
                                    "VAR   30","ID(str)     34","ASSIGN   38",
                                    "STRING(YwOvzHA(\226\132\150O9f3S)     41","VAR   61","ID(str)     65",
                                    "ASSIGN   69","STRING(EHWik64007tRF%&od=syG?+SQXbE^/)     72","EOF   106"]);

Test.lexer_test("ql143_test4.tig", ["VAR   2","ID(str1)     6","ASSIGN   11","STRING(normal string\n)     14",
                                    "VAR   33","ID(str2)     37","ASSIGN   42",
                                    "STRING(normal \n string)     45","VAR   65","ID(str3)     69",
                                    "ASSIGN   74","STRING(\nnormal string)     77","EOF   95"]);

Test.lexer_test("ql143_test5.tig", ["ID(val)     2","ID(str1)     6","ASSIGN   11",
                                    "STRING(\tnormal string)     14","ID(val)     33","ID(str2)     37",
                                    "ASSIGN   42","STRING(normal\tstring)     45","ID(val)     63",
                                    "ID(str3)     67","ASSIGN   72","STRING(normal string\t)     75",
                                    "EOF   93"]);

Test.lexer_test("ql143_test6.tig", ["ID(val)     2","ID(str)     6","ASSIGN   10","STRING(\"abc\")     13",
                                    "SEMICOLON   22","ID(val)     25","ID(str)     29","ASSIGN   33",
                                    "STRING(\"abc\"\n\t)     36","SEMICOLON   49","EOF   51"]);

Test.lexer_test("ql143_test7.tig", ["ID(val)     2","ID(str)     6","ASSIGN   10","STRING(\\string)     13",
                                    "ID(val)     25","ID(str)     29","ASSIGN   33",
                                    "STRING(\\string\\)     36","ID(val)     50","ID(str)     54",
                                    "ASSIGN   58","STRING(\\str\\ing\\\n)     61","EOF   78"]);

Test.lexer_test("ql143_test8.tig", ["STRING(asx\b{)     2","EOF   15"]);

Test.lexer_test("ql143_test9.tig", ["STRING(123)     2","EOF   11"]);


Test.lexer_test("ql143_test10.tig", ["LET   56","TYPE   61","ID(myint)     66","EQ   72","ID(int)     74",
                                    "TYPE   79","ID(arrtype)     85","EQ   93","ARRAY   95","OF   101",
                                    "ID(myint)     104","VAR   112","ID(arr1)     116","COLON   120",
                                    "ID(arrtype)     121","ASSIGN   129", "ID(arrtype)     132", "LBRACK   140",
                                    "INT(10)   141", "RBRACK   143", "OF   145", "INT(0)   148", "IN   150",
                                    "ID(arr1)     154", "END   159", "EOF   163"]);



