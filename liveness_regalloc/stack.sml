signature STACK =
sig
  type 'a stack
  val empty: 'a stack
  val push: 'a stack * 'a -> 'a stack
  val pop: 'a stack -> 'a stack
  val top: 'a stack -> 'a option
  val size: 'a stack -> int
  val listItems: 'a stack -> 'a list

end

structure Stack :> STACK =
struct
type 'a stack = 'a list
val empty : 'a stack = []
fun push (stack, ele) = ele :: stack
fun pop ([]) = []
  | pop (a::l) = l

fun top ([]) = NONE
  | top (a::l) = SOME a

fun size (stack) = List.length stack

fun listItems (stack) = stack

end
