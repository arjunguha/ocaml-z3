ocaml-z3
==============

An OCaml interface to the Z3 SMT solver

Temporary build steps
---------------------

From the project's root directory:
 - ```ocamlbuild -use-ocamlfind -classic-display -pkg ppx_jane -pkg unix -tag debug -tag annot -tag bin_annot -tag short_paths lib/Smtlib.native```
