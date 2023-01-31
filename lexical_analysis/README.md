## Documentation

### How we handle comments

Besides from INITIAL start state, we also created a COMMENT start state.

Every time we see a "/*" in the INITIAL state,we move into the COMMENT state. Because tiger language supports nested comments, we use a variable to count the comment depth.

Each time we encounter a '/\*' we increase the depth by 1. If we encounter a "\*/", we will reduce it by 1.

We jump out of COMMETN state to INTIAL state if and only if we encountered a "\*/" and the comment depth is equal to 0.

### How we handle strings

To handle strings, we created two starting state STRING and ESCAPE.

We have a reference to empty str initially. Let's call it ans.

When we see a " in the INITIAL state, we enter into STRING state.

In STRING state, for every symbol we meet if it is not "\", we concatinate it to str.

For the easy escape sequence like "\n", "\t", "\\", "\"", we can match and concatnate them easily with String.fromString function.

For escape sequence like "\^c" and "\ddd", we need to check its validiaty use String.fromString. If the function return NONE, then we report illegal escape sequence and continue. else if the function returns SOME ?, we concatinate it to ans.

Another difficult escape sequence is "\f___f\", if we see a "\" in the STRING state we also enter into ESCAPE state (NFA allows us to stay in two different states).

In ESCAPE state, we only want to match white space like (\n, \t, \r, \f ...) and continue.

If we matched another "\", we jump out of ESCAPE state and enter into STRING state to match the rest of the string.

If we matched with anything else, we know this escape sequence is illegal and report an error. If we find an error, we jump out of the ESCAPE state and return back to STRING state.

The following table, gives you explanation about escape sequences we handle.

| escape sequences | meaning                                                      | finsihed |
|:----------------:|:------------------------------------------------------------:|----------|
| \n               | A character interpreted by the system as end-of-line.        | yes      |
| \t               | Tab                                                          | yes      |
| \^c              | The control character c, for any appropriate c.              | yes      |
| \ddd             | The single character with ASCII code ddd (3 decimal digits). | yes      |
| \"               | The double-quote character (")                               | yes      |
| \\               | The backslash character (\).                                 | yes      |
| \f___f\          | noted below                                                  | yes      |


```
\f___f\

This sequence is ignored, where f f stands for
a sequence of one or more formatting characters (a subset of
the non-printable characters including at least space, tab,
newline, formfeed). This allows one to write long strings
on more than one line, by writing \ at the end of one line
and at the start of the next.

```

### Error Handling

When we encounter an error, we use the Errormsg.error function to print the line and column where the error occured.


For unclosed-string and unclosed-comment, this two errors will lead the parser remain in the STRING state or COMMENT state until eof.

So we will check this two errors in the eof function.

### End-of-file Handling

We return a EOF tokens in the eof function to denote end of file.

### Other Interesting Features of Our Lexer


# lex regexp

## reserved words
while, for, to, break, let, in, end, function, var, type, array, if, then, else, do, of, nil

## Identifiers
An identifier is a sequence of letters, digits, and underscores, starting with a letter. Uppercase letters are distinguished from lowercase.

	regexp: [a-zA-Z][a-zA-Z0-9_]*

## Comments
A comment may appear between any two tokens. Comments start with /* and end with */ and may be nested.

How to handle comments: described above.

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

