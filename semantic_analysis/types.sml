structure Types =
struct

type unique = unit ref

datatype ty =
         RECORD of (Symbol.symbol * ty) list * unique
         | NIL
         | INT
         | STRING
         | ARRAY of ty * unique
	 | NAME of Symbol.symbol * ty option ref
         | UNIT
         | IMPOSSIBILITY


fun name (RECORD(_, ref')) = "RECORD@" ^ (Word.toString (Unsafe.cast ref'))
  | name (NIL) = "NIL"
  | name (INT) = "INT"
  | name (STRING) = "STRING"
  | name (ARRAY(_, ref')) = "ARRAY@" ^ (Word.toString (Unsafe.cast ref'))
  | name (NAME(_, _)) = "NAME"
  | name (UNIT) = "UNIT"
  | name (IMPOSSIBILITY) = "IMPOSSIBILITY"

end

