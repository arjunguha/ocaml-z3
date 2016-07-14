(** An OCaml API for working with SMT-LIB-based solvers, such as Z3. *)

(** {1 Starting solvers.} *)

(** A handle to a Z3 process. *)
type solver

(** [make_solver path] produces a handle to a Z3 process.

  The argument [path] must be the path to the Z3 executable. If [z3] is on the
  [PATH], this can just be ["z3"].

  This command starts Z3 with the flags [-in] and [-smt2]. *)
val make_solver : string -> solver

(** {1 High-level API.}

 This high-level API to Z3 provides simple functions to construct
 terms and send commands to Z3. If Z3 produces an error in response to a
 command, that error is raised as an OCaml exception.
*)


type identifier =
  | Id of string [@@deriving sexp, compare]

type sort =
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int

type term =
  | String of string
  | Int of int
  | BitVec of int * int
  | Const of identifier
  | App of identifier * term list
  | Let of string * term * term [@@deriving sexp, compare]

type check_sat_result =
  | Sat
  | Unsat
  | Unknown

(** [declare_const solver x sort] runs the command [(declare-const x sort)] *)
val declare_const : solver -> identifier -> sort -> unit

(** [declare_fun solver x sorts sort] runs the command [(declare-fun x sorts sort)] *)
val declare_fun : solver -> identifier -> sort list -> sort -> unit

(** [declare_sort solver x arity] runs the command [(declare-sort x arity)] *)
val declare_sort : solver -> identifier -> int -> unit

(** [assert_ solver term] runs the command [(assert term)] *)
val assert_ : solver -> term -> unit

(** [check_sat solver] runs the command [(check-sat)] *)
val check_sat : solver -> check_sat_result

(** [get_model solver] runs the command [(get-model)] *)
val get_model : solver -> (identifier * term) list

(** [get_one_value solver e] runs the command [(get-value e)] *)
val get_one_value : solver -> term -> term

(** [push solver] runs the command [(push)] *)
val push : solver -> unit

(** [pop solver] runs the command [(pop)] *)
val pop : solver -> unit

(** The expression [Int] for the solver. *)
val int_sort : sort

(** The expression [Bool] for the solver. *)
val bool_sort : sort

(** [array_sort dom range] produces [(array dom range)] *)
val array_sort : sort -> sort -> sort


val int_to_term : int -> term

val bool_to_term : bool -> term

(** [const x] produces [Const (Id x)], which represents a reference to a
    variable declared with [(declare-const x sort)] *)
val const : string -> term

(** [equals e1 e2] produces [(= e1 e2)] *)
val equals : term -> term -> term

(** [and e1 e2] produces [(and e1 e2)]. In addition, nested [and]s are flattened
    to make debugging easier. *)
val and_ : term -> term -> term

(** [or e1 e2] produces [(or e1 e2)]. In addition, nested [or]s are flattened
    to make debugging easier. *)
val or_ : term -> term -> term

(** [not e] produces [(not e)]. *)
val not_ : term -> term

(** [ite e1 e2 e3] produces [(ite e1 e2 e3)] *)
val ite : term -> term -> term -> term

(** [implies e1 e2] produces [(=> e1 e2)]. *)
val implies : term -> term -> term

(** [add e1 e2] produces [(+ e1 e2)]. *)
val add : term -> term -> term

(** [sub e1 e2] produces [(- e1 e2)]. *)
val sub : term -> term -> term

(** [mul e1 e2] produces [( * e1 e2)]. *)
val mul : term -> term -> term

(** [lt e1 e2] produces [(< e1 e2)]. *)
val lt : term -> term -> term

(** [> e1 e2] produces [(> e1 e2)]. *)
val gt : term -> term -> term

(** [lte e1 e2] produces [(<= e1 e2)]. *)
val lte : term -> term -> term

(** [gte e1 e2] produces [(>= e1 e2)]. *)
val gte : term -> term -> term

(** {1 Bit-Vectors} *)

(** [bv_sort n] produces [(_ BitVec n)]. *)
val bv_sort : int -> sort

(** [bv n w] produces a bit-vector of width [w] that represents the integer [n]. *)
val bv : int -> int -> term

val bvadd : term -> term -> term
val bvsub : term -> term -> term
val bvmul : term -> term -> term
val bvurem : term -> term -> term
val bvsrem : term -> term -> term
val bvsmod : term -> term -> term
val bvshl : term -> term -> term
val bvlshr : term -> term -> term
val bvashr : term -> term -> term
val bvor : term -> term -> term
val bvand : term -> term -> term
val bvnand : term -> term -> term
val bvnor : term -> term -> term
val bvxnor : term -> term -> term
val bvudiv : term -> term -> term
val bvsdiv : term -> term -> term
val bvneg : term -> term
val bvnot : term -> term

(** {1 Low-level interface} *)

(** The variant of s-expressions used by SMT-LIB. *)
type sexp = Smtlib_syntax.sexp =
  | SList of sexp list
  | SSymbol of string
  | SString of string
  | SKeyword of string
  | SInt of int
  | SBitVec of int * int

(** [command solver sexp] sends a command to the solver and reads a response. *)
val command : solver -> sexp -> sexp

(** [term_to_sexp term] returns the term as an s-expression. *)
val term_to_sexp : term -> sexp

(** [sexp_to_string sexp] returns the s-expressions as a string. *)
val sexp_to_string : sexp -> string

(** [fresh_name base] returns a fresh symbol given a base name. *)
val fresh_name : string -> sexp
