{
  open Lexing
  open Smtlib_parser

  let parse_hex (str : string) : (int * int) =
    let len = (String.length str) - 2 in
    let str = "0x" ^ (String.sub str 2 len) in
    (int_of_string str, len * 4)
  let parse_bin (str : string) : (int * int) =
    let len = (String.length str) - 2 in
    let str = "0b" ^ (String.sub str 2 len) in
    (int_of_string str, len ) 
}

let simple_symbol_char = [ 'A'-'Z' 'a'-'z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']
let simple_symbol = simple_symbol_char (['0' - '9'] | simple_symbol_char )*
let keyword = ':' simple_symbol
let blank = [ ' ' '\t' ]
let numeral = (( ['-']?['1'-'9']['0'-'9']* ) | ['0'])
let hex_int = "#x" [ '0'-'9' 'a'-'f' ]+
let bin_int = "#b" ['0'-'1']+
let string = ("\\\"" | [^ '"'])*

rule token = parse
  | ";" [^ '\n' '\r']+ { token lexbuf }
  | "\r\n" { new_line lexbuf; token lexbuf }
  | "\n" { new_line lexbuf; token lexbuf }
  | blank+ { token lexbuf }
  | eof { EOF }
  | numeral as n { INT (int_of_string n) }
  | hex_int as str { let (n, w) = parse_hex str in HEX (n, w) }
  | bin_int as str { let (n, w) = parse_bin str in HEX (n,w) }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "\"" (string as x) "\"" { STRING x }
  | simple_symbol as x { SYMBOL x }
  | keyword as x { KEYWORD x }

and block_comment = parse
  | "*/" { token lexbuf }
  | "*" { block_comment lexbuf }
  | "\r\n" { new_line lexbuf; block_comment lexbuf }
  | "\n" { new_line lexbuf; block_comment lexbuf }
  | ([^ '*' '\n'])+  { block_comment lexbuf }
