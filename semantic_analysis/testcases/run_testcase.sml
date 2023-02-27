CM.make "../sources.cm";
use "../semant.sml";

(* run all provided test cases *)
fun run_tests (counter_start) =
let
  val counter = ref counter_start
in
  while !counter < 50 do (
    print("now testing file: test" ^ Int.toString(!counter) ^ ".tig\n");
    Main.compile ("../../testcases/test" ^ Int.toString(!counter) ^ ".tig");
    counter := !counter + 1
  )
end;

print("now testing file: merge.tig\n");
Main.compile "../../testcases/merge.tig";
print("now testing file: queens.tig\n");
Main.compile "../../testcases/queens.tig";
run_tests(1);
