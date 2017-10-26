include Smtlib_syntax

type solver = { stdin : out_channel; stdout : in_channel; stdout_lexbuf : Lexing.lexbuf }

(* Does not flush *)
let rec write_sexp (out_chan : out_channel) (e : sexp): unit = match e with
  | SInt n -> output_string out_chan (string_of_int n)
  | SBitVec (n, w) -> Printf.fprintf out_chan "(_ bv%d %d)" n w
  | SBitVec64 n -> Printf.fprintf out_chan "(_ bv%Ld 64)" n
  | SSymbol str -> output_string out_chan str
  | SKeyword str -> output_string out_chan str
  | SString str ->
    (output_char out_chan '(';
     output_string out_chan str;
     output_char out_chan ')')
  | SList lst ->
    (output_char out_chan '(';
     write_sexp_list out_chan lst;
     output_char out_chan ')')

and write_sexp_list (out_chan : out_channel) (es : sexp list) : unit =
  match es with
    | [] -> ()
    | [e] -> write_sexp out_chan e
    | e :: es ->
      (write_sexp out_chan e;
       output_char out_chan ' ';
       write_sexp_list out_chan es)

let write (solver : solver) (e : sexp) : unit =
  write_sexp solver.stdin e;
  output_char solver.stdin '\n';
  flush solver.stdin

let read (solver : solver) : sexp =
  Smtlib_parser.sexp Smtlib_lexer.token solver.stdout_lexbuf

let command (solver : solver) (sexp : sexp) = write solver sexp; read solver

let silent_command (solver : solver) (sexp : sexp) = write solver sexp

let print_success_command =
  SList [SSymbol "set-option"; SKeyword ":print-success"; SSymbol "true"]

(* keep track of all solvers we spawn, so we can close our read/write
   FDs when the solvers exit *)
let _solvers : (int * solver) list ref = ref []

module StringMap = Map.Make(String)

let _names :  (solver * int StringMap.t ref) list ref = ref []

let handle_sigchild (_ : int) : unit =
  if List.length !_solvers = 0
  then ignore @@ Unix.waitpid [] (-1)
  else
    begin
      let open Printf in
      let (pid, status) = Unix.waitpid [] (-1) in
      eprintf "solver child (pid %d) exited\n%!" pid;
      try
        let solver = List.assoc pid !_solvers in
        close_in_noerr solver.stdout; close_out_noerr solver.stdin
      with
        _ -> ()
    end

let () =
  Sys.set_signal Sys.sigchld (Sys.Signal_handle handle_sigchild)

let make_solver (z3_path : string) : solver =
  let open Unix in
  let (z3_stdin, z3_stdin_writer) = pipe () in
  let (z3_stdout_reader, z3_stdout) = pipe () in
  (* If the ocaml ends of the pipes aren't marked close-on-exec, they
     will remain open in the fork/exec'd z3 process, and z3 won't exit
     when our main ocaml process ends. *)
  let _ = set_close_on_exec z3_stdin_writer; set_close_on_exec z3_stdout_reader in
  let pid = create_process z3_path [| z3_path; "-in"; "-smt2" |]
    z3_stdin z3_stdout stderr in
  let in_chan = in_channel_of_descr z3_stdout_reader in
  let out_chan = out_channel_of_descr z3_stdin_writer in
  set_binary_mode_out out_chan false;
  set_binary_mode_in in_chan false;
  let solver = { stdin = out_chan; stdout = in_chan; stdout_lexbuf = Lexing.from_channel in_chan } in
  _solvers := (pid, solver) :: !_solvers;
  _names := (solver, ref StringMap.empty) :: !_names;
  try
    match command solver print_success_command with
      | SSymbol "success" -> solver
      | _ -> failwith "could not configure solver to :print-success"
  with
    Sys_error ("Bad file descriptor") -> failwith "couldn't talk to solver, double-check path"

let sexp_to_string (sexp : sexp) : string =
  let open Buffer in
  let buf = create 100 in
  let rec to_string (sexp : sexp) : unit = match sexp with
    | SList alist -> add_char buf '('; list_to_string alist; add_char buf ')'
    | SSymbol x -> add_string buf x;
    | SKeyword x -> add_string buf x;
    | SString x -> add_char buf '"'; add_string buf x; add_char buf '"'
    | SInt n -> add_string buf (string_of_int n)
    | SBitVec (n, w) -> add_string buf (Format.sprintf "(_ bv%d %d)" n w)
    | SBitVec64 n -> add_string buf (Format.sprintf "(_ bv%Ld 64)" n)
  and list_to_string (alist : sexp list) : unit = match alist with
    | [] -> ()
    | [x] -> to_string x
    | x :: xs -> to_string x; add_char buf ' '; list_to_string xs in
  to_string sexp;
  contents buf

let fresh_name (solver : solver) (base : string) : sexp =
  let names =
    try
      List.assoc solver !_names
    with _ -> failwith "Z3 instance doesn't have an associated fresh_name map" in
  try
    let n = StringMap.find base !names in
    names := StringMap.add base (n+1) !names;
    SSymbol (base ^ (string_of_int n))
  with
    Not_found ->
    names := StringMap.add base 1 !names;
    SSymbol (base ^ "0")

type check_sat_result =
  | Sat
  | Unsat
  | Unknown

type identifier =
  | Id of string

type sort =
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int

type term =
  | String of string
  | Int of int
  | BitVec of int * int
  | BitVec64 of int64
  | Const of identifier
  | App of identifier * term list
  | Let of string * term * term

type tactic =
  | Simplify
  | SolveEQs
  | BitBlast
  | AIG
  | SAT
  | SMT
  | QFBV
  | UsingParams of tactic * (string * bool) list
  | Then of tactic list

let rec tactic_to_sexp (t : tactic) : sexp = match t with
  | Simplify ->
    SSymbol "simplify"
  | SolveEQs ->
    SSymbol "solve-eqs"
  | BitBlast ->
    SSymbol "bit-blast"
  | AIG ->
    SSymbol "aig"
  | SAT ->
    SSymbol "sat"
  | SMT ->
    SSymbol "smt"
  | QFBV ->
    SSymbol "qfbv"
  | UsingParams (t', params) ->
    let param_to_sexp (keyword, value) =
      [ SKeyword keyword; SSymbol (string_of_bool value) ] in
    SList ((SSymbol "using-params") :: (tactic_to_sexp t')
           :: (List.concat @@ List.map param_to_sexp params))
  | Then ts ->
    SList ((SSymbol "then") :: List.map tactic_to_sexp ts)

let id_to_sexp (id : identifier) : sexp = match id with
  | Id x -> SSymbol x

let rec sort_to_sexp (sort : sort) : sexp = match sort with
  | Sort x -> id_to_sexp x
  | SortApp (x, sorts) ->
    SList ((id_to_sexp x) :: (List.map sort_to_sexp sorts))
  | BitVecSort n -> SList [ SSymbol "_"; SSymbol "BitVec"; SInt n ]

let rec term_to_sexp (term : term) : sexp = match term with
  | String s -> SString s
  | Int n -> SInt n
  | BitVec (n, w) -> SBitVec (n, w)
  | BitVec64 n -> SBitVec64 n
  | Const x -> id_to_sexp x
  | App (f, args) -> SList (id_to_sexp f :: (List.map term_to_sexp args))
  | Let (x, term1, term2) ->
    SList [SSymbol "let";
           SList [SList [SSymbol x; term_to_sexp term1]];
           term_to_sexp term2]

let rec sexp_to_term (sexp : sexp) : term = match sexp with
  | SString s -> String s
  | SInt n -> Int n
  | SBitVec (n, w) -> BitVec (n, w)
  | SBitVec64 n -> BitVec64 n
  | SSymbol x -> Const (Id x)
  | SList (SSymbol "-" :: SInt x :: []) -> Int (-x)
  | _ -> failwith "unparsable term"

let expect_success (solver : solver) (sexp : sexp) : unit =
  match command solver sexp with
  | SSymbol "success" -> ()
  | SList [SSymbol "error"; SString x] -> failwith x
  | sexp -> failwith ("expected either success or error from solver, got " ^
                      (sexp_to_string sexp))

let declare_const (solver : solver) (id : identifier) (sort : sort) : unit =
  expect_success solver
    (SList [SSymbol "declare-const"; id_to_sexp id; sort_to_sexp sort])

let declare_fun (solver : solver) (id : identifier) (args : sort list) (sort : sort) : unit =
  expect_success solver
    (SList ([SSymbol "declare-fun"; id_to_sexp id; SList (List.map (fun s -> sort_to_sexp s) args); sort_to_sexp sort]))

let declare_sort (solver : solver) (id : identifier) (arity : int) : unit =
  expect_success solver
    (SList [SSymbol "declare-sort"; id_to_sexp id; SInt arity])

let assert_ (solver : solver) (term : term) : unit =
  expect_success solver (SList [SSymbol "assert"; term_to_sexp term])

let assert_soft (solver : solver) ?weight:(weight = 1) ?id:(id = "") (term : term) : unit =
  let id_suffix = match id with
    | "" -> []
    | _ -> [SKeyword ":id"; SSymbol id] in
  let sexp =
    (SList ([SSymbol "assert-soft"; term_to_sexp term; SKeyword ":weight"; SInt weight] @ id_suffix)) in
  silent_command solver sexp

let maximize (solver : solver) (term : term) : unit =
  silent_command solver (SList ([SSymbol "maximize"; term_to_sexp term]))

let minimize (solver : solver) (term : term) : unit =
  silent_command solver (SList ([SSymbol "minimize"; term_to_sexp term]))

let read_objectives (solver : solver) : unit =
  match read solver with
  | SList [SSymbol "objectives"; SList l] -> ()
  | s -> failwith ("unexpected result in optimized objective, got " ^ sexp_to_string s)

let rec check_sat (solver : solver) : check_sat_result =
  let fail sexp  = failwith ("unexpected result from (check-sat), got " ^
                       sexp_to_string sexp) in
  let rec read_sat sexp =
    let match_map () = match read solver with
      | SInt n ->
        read_sat @@ read solver
      | sexp ->
        fail sexp in
    match sexp with
    | SSymbol "sat" -> Sat
    | SSymbol "unsat" -> Unsat
    | SSymbol "unknown" -> Unknown
    | SSymbol "|->" -> match_map ()
    | SSymbol sym -> read_sat @@ read solver
    | SList sexp -> read_sat @@ read solver
    | sexp -> failwith ("unexpected result from (check-sat), got " ^
                        sexp_to_string sexp) in
  read_sat @@ command solver (SList [SSymbol "check-sat"])

let rec check_sat_using (tactic : tactic) (solver : solver) : check_sat_result =
  let fail sexp  = failwith ("unexpected result from (check-sat-using), got " ^
                       sexp_to_string sexp) in
  let rec read_sat sexp =
    let match_map () = match read solver with
      | SInt n ->
        read_sat @@ read solver
      | sexp ->
        fail sexp in
    match sexp with
    | SSymbol "sat" -> Sat
    | SSymbol "unsat" -> Unsat
    | SSymbol "unknown" -> Unknown
    | SSymbol "|->" -> match_map ()
    | SSymbol sym -> read_sat @@ read solver
    | SList sexp -> read_sat @@ read solver
    | sexp -> failwith ("unexpected result from (check-sat-using), got " ^
                        sexp_to_string sexp) in
  let cmd = (SList [SSymbol "check-sat-using"; tactic_to_sexp tactic]) in
  read_sat @@ command solver cmd

let get_model (solver : solver) : (identifier * term) list =
  let rec read_model sexp = match sexp with
    | [] -> []
    | (SList [SSymbol "define-fun"; SSymbol x; SList []; _; sexp]) :: rest ->
      (Id x, sexp_to_term sexp) :: read_model rest
    | _ :: rest -> read_model rest in
  match command solver (SList [SSymbol "get-model"]) with
  | SList (SSymbol "model" :: alist) -> read_model alist
  | sexp -> failwith ("expected model, got " ^ (sexp_to_string sexp))

let get_one_value (solver : solver) (e : term) : term =
  let res = command solver
      (SList [SSymbol "get-value"; SList [term_to_sexp e]]) in
  match res with
  | SList [SList [_; x]] -> sexp_to_term x
  | sexp -> failwith ("expected a single pair, got " ^
                      (sexp_to_string sexp))

let push (solver : solver) = expect_success solver (SList [SSymbol "push"])
let pop (solver : solver) = expect_success solver (SList [SSymbol "pop"])

let int_sort  = Sort (Id "Int")

let bool_sort = Sort (Id "Bool")

let array_sort dom rng = SortApp (Id "Array", [dom; rng])

let bv_sort w = BitVecSort w

let int_to_term n = Int n

let const x = Const (Id x)

let bool_to_term b = match b with
  | true -> Const (Id "true")
  | false -> Const (Id "false")

let app2 x term1 term2 = App (Id x, [term1; term2])

let app1 x term = App (Id x, [term])

let equals = app2 "="

let and_ term1 term2 = match (term1, term2) with
  | (App (Id "and", alist1), App (Id "and", alist2)) -> App (Id "and", alist1 @ alist2)
  | (App (Id "and", alist1), _) -> App (Id "and", alist1 @ [ term2 ])
  | (_, App (Id "and", alist2)) -> App (Id "and", term1 :: alist2)
  | _ -> App (Id "and", [term1; term2])

let or_ term1 term2 = match (term1, term2) with
  | (App (Id "or", alist1), App (Id "or", alist2)) -> App (Id "or", alist1 @ alist2)
  | (App (Id "or", alist1), _) -> App (Id "or", alist1 @ [ term2 ])
  | (_, App (Id "or", alist2)) -> App (Id "or", term1 :: alist2)
  | _ -> App (Id "or", [term1; term2])

let xor term1 term2 = match term1, term2 with
  | (App (Id "xor", alist1), App (Id "xor", alist2)) -> App (Id "xor", alist1 @ alist2)
  | (App (Id "xor", alist1), _) -> App (Id "xor", alist1 @ [ term2 ])
  | (_, App (Id "xor", alist2)) -> App (Id "xor", term1 :: alist2)
  | _ -> App (Id "xor", [term1; term2])

let not_ term = App (Id "not", [term])

let ite e1 e2 e3 = App (Id "ite", [e1; e2; e3])

let implies = app2 "=>"

let add = app2 "+"

let sub = app2 "-"

let mul = app2 "*"

let lt = app2 "<"

let gt = app2 ">"

let lte = app2 "<="

let gte = app2 ">="

let bv n w = BitVec (n, w)

let bv64 n = BitVec64 n

let bvadd = app2 "bvadd"
let bvsub = app2 "bvsub"
let bvmul = app2 "bvmul"
let bvurem = app2 "bvurem"
let bvsrem = app2 "bvsrem"
let bvsmod = app2 "bvsmod"
let bvshl = app2 "bvshl"
let bvlshr = app2 "bvlshr"
let bvashr = app2 "bvashr"
let bvor = app2 "bvor"
let bvand = app2 "bvand"
let bvnand = app2 "bvnand"
let bvnor = app2 "bvnor"
let bvxnor = app2 "bvxnor"
let bvudiv = app2 "bvudiv"
let bvsdiv = app2 "bvsdiv"
let bvugt = app2 "bvugt"
let bvuge = app2 "bvuge"
let bvult = app2 "bvult"
let bvule = app2 "bvule"
let bvneg = app1 "bvneg"
let bvnot = app1 "bvnot"
