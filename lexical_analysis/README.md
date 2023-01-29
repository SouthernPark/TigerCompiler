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

	regexp: [a-zA-Z][a-zA-Z0-9_]*

## Comments
A comment may appear between any two tokens. Comments start with /* and end with */ and may be nested.

Using YYBEGIN and changable start state to deal with possible nested comments. (Described in page 31 of the book)

To implement nested comment, we need to count the number lett /* and right */ (we only exit the COMMET state when the count matches)

### valid comments

```
/* valid comments */

/* comment */ */ (regard as valid, the last */ will be regared as TIME and DIVIDE)

/**/* abc */ def */ (regard as valid. the first 4 chars will be regared as comments, the rest will either be ws, id, time or divide)

 (This case is the same as the second case)
```

### invalid comments

```
/* /*  */ will be regarded Unclosed Comment

/*///*/ will be regarded as Unclosed Comment

```

## Integer literal

A sequence of decimal digits is an integer constant that denotes the corresponding integer value.

```
regexp: [0-9]+
```

## String literal
The string value that you return for a string literal should have all the escape sequences translated into their meanings.

Defined in page 516

A string constant is a sequence, between quotes ("), of zero or more printable characters, spaces, or escape sequences. Each escape sequence is introduced by the escape character \, and stands for a character sequence. The allowed escape sequences are as follows (all other uses of \ being illegal):

| escape sequences | meaning                                                      | finsihed |
|:----------------:|:------------------------------------------------------------:|----------|
| \n               | A character interpreted by the system as end-of-line.        | yes      |
| \t               | Tab                                                          | yes      |
| \^c              | The control character c, for any appropriate c.              | yes      |
| \ddd             | The single character with ASCII code ddd (3 decimal digits). | yes      |
| \"               | The double-quote character (")                               | yes      |
| \\               | The backslash character (\).                                 | yes      |
| \f___f\          | noted below                                                  | yes      |


The last escape sequence is as below:

```
\f___f\

This sequence is ignored, where f f stands for
a sequence of one or more formatting characters (a subset of
the non-printable characters including at least space, tab,
newline, formfeed). This allows one to write long strings
on more than one line, by writing \ at the end of one line
and at the start of the next.

```

all other uses of \ being illegal

Resouces explain the "\^c" control character:

[control_character](https://www.geeksforgeeks.org/control-characters/ "control_character")

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

