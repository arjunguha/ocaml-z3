%{
open Smtlib_syntax
%}

%token LPAREN RPAREN
%token<string> STRING
%token<string> SYMBOL
%token<string> KEYWORD
%token<int> INT
%token<int * int> HEX
%token EOF

%start sexp
%type <Smtlib_syntax.sexp> sexp

%%

sexp_list :
  | { [] }
  | sexp sexp_list { $1 :: $2 }

sexp :
  | INT { SInt $1 }
  | HEX { let (n, w) = $1 in SBitVec (n, w) }
  | STRING { SString $1 }
  | SYMBOL { SSymbol $1 }
  | KEYWORD { SKeyword $1 }
  | LPAREN sexp_list RPAREN { SList $2 }

%%
