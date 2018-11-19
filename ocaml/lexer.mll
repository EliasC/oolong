{
  open Parser

  let mk_id = function
    | "async" -> Parser.ASYNC
    | "class" -> Parser.CLASS
    | "def" -> Parser.DEF
    | "extends" -> Parser.EXTENDS
    | "finish" -> Parser.FINISH
    | "implements" -> Parser.IMPLEMENTS
    | "in" -> Parser.IN
    | "interface" -> Parser.INTERFACE
    | "let" -> Parser.LET
    | "lock" -> Parser.LOCK
    | "new" -> Parser.NEW
    | "null" -> Parser.NULL

    | "=" -> Parser.EQ
    | "(" -> Parser.LPAREN
    | ")" -> Parser.RPAREN
    | "{" -> Parser.LBRACE
    | "}" -> Parser.RBRACE
    | ":" -> Parser.COLON
    | ";" -> Parser.SEMI
    | "," -> Parser.COMMA
    | "." -> Parser.DOT

    | s -> Parser.IDENT s

  let mk_int n = Parser.INT (int_of_string n)
}

let whitespace = (' ' | '\t' | '\n')
let letter = ['a'-'z'] | ['A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | '_' | digit)*
let number = digit+
let symbol = '=' | '(' | ')' | '{' | '}' | ':' | ';' | ',' | '.' | '+' | '-'
rule main = parse
  | whitespace+ { main lexbuf }
  | (ident | symbol) as s { mk_id s }
  | number as n { mk_int n }
  | eof { Parser.EOF }
{ }
