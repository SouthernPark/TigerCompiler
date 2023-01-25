## Documentation

### How we handle comments

### How we handle strings

### Error Handling

### End-of-file Handling

### Other Interesting Features of Our Lexer


# lex regexp

## reserved words
while, for, to, break, let, in, end, function, var, type, array, if, then, else, do, of, nil

## Identifiers
An identifier is a sequence of letters, digits, and underscores, starting with a letter. Uppercase letters are distinguished from lowercase.

## Comments
A comment may appear between any two tokens. Comments start with /* and end with */ and may be nested.


## Integer literal

## String literal
The string value that you return for a string literal should have all the escape sequences translated into their meanings.

## puctuation symbols
, : ; ( ) [ ] { } . + - * / = <> < <= > >= & | :=

## negative value
There are no negative integer literals; return two separate tokens for -32.

## unclosure
Detect unclosed comments (at end of file) and unclosed strings.


# testcases
The directory $TIGER/testeases contains a few sample Tiger programs:

[tiger_testcases](https://www.cs.princeton.edu/~appel/modern/testcases/ "tiger_testcases")

Make a file test.tig containing a short program in the Tiger language. Then execute sml and type the command CM.make();

The CM (compilation manager) make system will run ml-lex, if needed, and will compile and link the ML source files (as needed).

Finally, Parse.parse "test.tig" will lexically analyze the file using a test scaffold.

