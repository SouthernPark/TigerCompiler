# TigerCompiler
Developers:
Yinchao Shi (ys322)
Qiangqiang Liu (ql143)
Wangkai Jin (wj78)

# Book Used
[Modern Compiler Implementation in ML](https://www.cs.princeton.edu/~appel/modern/ml/ "Modern Compiler Implementation in ML")

# Chapters

Below mapped some chaptter program assignment to our git repo:

[chapter2 lexical_analysis](./lexical_analysis "chapter2 lexical_analysis") \
[chapter3&4 parsing, abstract_syntax](./parser "chapter3&4 parsing, abstract_syntax") \
[chapter5 semantic_analysis](./semantic_analysis "chapter5 semantic_analysis") \
[chapter6&7 intermediate_representation](./intermediate_representation "chapter6&7 intermediate_representation") \
[chapter8&9 instruction_selection](./instruction_selection "chapter8&9 instruction_selection") \
[chapter10&11 liveness_analysis, register_allocation](./liveness_regalloc "chapter10&11 liveness_analysis, register_allocation") \
[chapter12 putting_it_all_together](./final_compiler "chapter12 putting_it_all_together")

[convert sml code to binary exetuable with mlton](./mlton_executable "convert sml code to binary exetuable with mlton")


# Improvement and Regrade
In semantic_analysis, we fixed two problems below, which can be tested in the final version code.
* Allowed duplicate names in mutually recursive function/type groups.
* Treatment of upcasting was not consistent. You did not allow expressions in while, for, or if-then statements to be upcast to UNIT, but you did allow if-then-else and procedure expressions to be implicitly upcast. You can choose if expressions can be implicitly upcast to unit or not, but regardless of your choice it has to be documented and consistent across all constructs.

# How to Compile

## run with sml compiler
<pre><code>
cd final_compiler/
rlwrap sml
CM.make "sources.cm";
Main.compile "../testcases/queens.tig";
</code></pre>
There are a list of test cases under the folder.
A mips assembly file will be generated, and then use QtSpim to run the assembly.

## run directly with mlton executable

The compile file under this top directory can be executed directly to compile a tiger file.

<pre><code>
cd mlton_executable
./compile testcases/queens.tig
</code></pre>
Compile the tiger file in "testcases/queens.tig" and produce "testcases/queens.tig"

You may compile multi tiger file in one command like below:
<pre><code>
./compile tiger_file1 tiger_file2 ...
</code></pre>

# how to run the compiled mips file
you may download the mips simpulator QtSpim if you CPU architecture is not mips from the following website:

https://sourceforge.net/projects/spimsimulator/files/

## process to run mips file

open QtSpim -> click File -> click Reinitialize and load file -> select the mips file -> click on the run button

If you want to see the output or give input, you need to use the console termianl.

To open console termianl if it's not set up on default: click window -> click console


