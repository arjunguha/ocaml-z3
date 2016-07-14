ocaml-z3
==============

An OCaml interface to the Z3 SMT solver

Temporary build steps
---------------------

From the project's root directory:
 - ```ocamlbuild -use-ocamlfind -classic-display -pkg ppx_jane -pkg unix -tag debug -tag annot -tag bin_annot -tag short_paths lib/Smtlib.native```


Installation with OPAM
----------------------

- Install [Git](https://git-scm.com/downloads)

  On Mac OS X, Git is included with [XCode](https://developer.apple.com/xcode/).

- Install [OPAM](https://opam.ocaml.org/doc/Install.html)

- From the command line, run:

  ```
  opam pin add z3 https://github.com/plasma-umass/ocaml-z3.git
  ```
