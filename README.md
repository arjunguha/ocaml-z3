ocaml-z3
==============

An OCaml interface to the Z3 SMT solver

Local build steps
---------------------

This package depends on the ```oasis``` build system being installed on your machine.

From the project's root directory:
  ```
  ./configure
  make build
  make install
  ```


Installation with OPAM
----------------------

- Install [Git](https://git-scm.com/downloads)

  On Mac OS X, Git is included with [XCode](https://developer.apple.com/xcode/).

- Install [OPAM](https://opam.ocaml.org/doc/Install.html)

- From the command line, run:

  ```
  opam pin add z3 https://github.com/plasma-umass/ocaml-z3.git
  ```
