signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val look  : 'a table * symbol -> 'a option
end

structure Symbol :> SYMBOL =
struct

type symbol = string * int

structure H = HashTable

exception Symbol
val nextsym = ref 0
val sizeHint = 128

val hashtable : (string,int) H.hash_table =
    H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)

(*
Every time you can Symbol.symbol(some_str)
it will check if some_str in hashtable or not
if there is no some_str then  insert (some_str, cur_index)
into hashtable, then incr index by 1

return symbol (which is type string*int )

symbol is usually var id, type id or func id => string
*)
fun symbol name =
    case H.find hashtable name
     of SOME i => (name,i)
      | NONE => let val i = !nextsym
	        in nextsym := i+1;
		   H.insert hashtable (name,i);
		   (name,i)
		end

fun name(s,n) = s

(* IntMapTable defined in table.sml *)
structure Table = IntMapTable(type key = symbol
			      fun getInt(s,n) = n)

type 'a table= 'a Table.table
val empty = Table.empty
val enter = Table.enter
val look = Table.look

end



