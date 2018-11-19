%{
open Ast
%}

/* Misc tokens */
%token EOF
%token <string> IDENT
%token <int> INT

/* Keywords */
%token ASYNC
%token CLASS
%token DEF
%token EXTENDS
%token FINISH
%token IMPLEMENTS
%token IN
%token INTERFACE
%token LET
%token LOCK
%token NEW
%token NULL

/* Symbolic Tokens */
%token EQ            /* "="  */
%token LPAREN        /* "("  */
%token RPAREN        /* ")"  */
%token LBRACE        /* "{"  */
%token RBRACE        /* "}"  */
%token COLON         /* ":"  */
%token SEMI          /* ";"  */
%token COMMA         /* ","  */
%token DOT           /* "."  */

%token PLUS          /* "+"  */
%token MINUS         /* "-"  */
%left PLUS
%left MINUS

%start main

%type <Ast.program> main

%%

main:
    | idefs cdefs expr EOF { Program ($1, $2, $3) }
;
idefs:
    | { [] }
    | idef idefs { $1 :: $2 }
idef:
    | INTERFACE IDENT LBRACE msigs RBRACE { InterfaceDef ($2, $4) }
    | INTERFACE IDENT EXTENDS IDENT COMMA IDENT { ExtInterfaceDef ($2, $4, $6) }
cdefs:
    | { [] }
    | cdef cdefs { $1 :: $2 }
cdef: CLASS IDENT IMPLEMENTS IDENT LBRACE
            fields mtds
            RBRACE { Ast.ClassDef ($2, $4, $6, $7) }
msigs:
    | { [] }
    | msig msigs { $1 :: $2 }
msig:
    | IDENT LPAREN IDENT COLON typ RPAREN COLON typ { Ast.MethodSig ($1, $3, $5, $8) }
fields:
    | { [] }
    | field fields { $1 :: $2 }
field:
    | IDENT COLON typ { FieldDef ($1, $3) }
mtds:
    | { [] }
    | mtd mtds { $1 :: $2 }
mtd:
    | DEF msig LBRACE expr RBRACE { MethodDef ($2, $4) }
;
expr:
    | NULL { Null }
    | IDENT { Var $1 }
    | INT { Int $1 }
    | expr PLUS expr { Add ($1, $3) }
    | expr MINUS expr { Sub ($1, $3) }
    | IDENT DOT IDENT { FieldAccess ($1, $3) }
    | IDENT DOT IDENT EQ expr { FieldUpdate ($1, $3, $5) }
    | IDENT DOT IDENT LPAREN expr RPAREN { MethodCall ($1, $3, $5) }
    | LET IDENT EQ expr IN expr { Let ($2, $4, $6) }
    | NEW IDENT { New $2 }
    | LPAREN typ RPAREN expr { Cast ($2, $4) }
    | FINISH LBRACE
             ASYNC LBRACE expr RBRACE
             ASYNC LBRACE expr RBRACE
             RBRACE SEMI expr
             { FinishAsync ($5, $9, $13) }
    | LOCK LPAREN IDENT RPAREN IN expr { Lock ($3, $6) }
typ:
    | IDENT { UnresolvedType $1 }
