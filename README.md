# LiveActris Artifact

A version of [LinearActris](https://doi.org/10.5281/zenodo.8422755) where Hoare triples not only guarantee the safety
properties of LinearActris (deadlock freedom and leak freedom) but also a new
liveness property: **weak normalization for sequential steps**. That is, at any
point during execution, it is always possible to make progress toward a state
that is either final (all values returned and the heap empty) or able to perform
a concurrent step. As a consequence, programs that do not use concurrency
terminate, since sequential execution is deterministic.

This artifact contains Rocq/Coq source code formalizing the logic and its
metatheory.

## Dependencies

This project depends on two main Coq libraries:

- **Iris**  
  A higher-order concurrent separation logic framework.  
  This project uses a **custom version of Iris**, included under the directory
  `iris/`. 

- **stdpp**  
  A general-purpose Coq library (sometimes called *std++*) providing finite maps,
  sets, lists, and many common mathematical constructions used throughout the
  development. This project uses a particular version of stdpp that is compatible
  with the custom Iris version, included under the directory `stdpp/`.

Both dependencies are built automatically when running `dune build`.

## Installation

This artifact has been tested with Coq 8.20.0 using dune. A custom version of
Iris is required, see below. 

1. Install `opam`. You can find the instructions on https://opam.ocaml.org/doc/Install.html
  Do not forget to use `opam init` and add `eval $(opam env)` to your `.bashrc` or `.zshrc` file. This makes the `coqc` command, and other commands installed by `opam`, available in your terminal.
2. Install `dune` as an opam package:

        opam install dune

3. Install `git`. You can find the instructions on https://git-scm.com/book/en/v2/Getting-Started-Installing-Git
3. Make a directory that will contain the artifact, and `cd` into it:

        mkdir artifact
        cd artifact

4. Download a custom version of Iris using

        git clone -b robbert/sbi https://gitlab.mpi-sws.org/iris/iris.git

5. Download a the exact same version of stdpp used in the artifact.

        git clone https://gitlab.mpi-sws.org/iris/stdpp.git
        cd stdpp
        git checkout cc5fd6238e71c43fabd3ed7428541ebca26b9cc4

6. Download and unzip the `sources.zip` file, and build it:

        unzip sources.zip
        dune build

## File Structure

The core of the artifact is contained in the folder **theories/**:

- **theories/prelude/**  
  Foundational definitions and general-purpose lemmas.

- **theories/algebra/**  
  Algebraic constructions used throughout the logic, including multisets.

- **theories/base_logic/**  
  The base program logic: adequacy, weakest-precondition rules, linear
  predicates, communication graphs, and auxiliary constructions.

- **theories/bi/**  
  Additional BI tools and constructions, including the least Banach fixpoint
  development.

- **theories/lang/**  
  The formal definition of the language (syntax, operational semantics,
  metatheory) and notations.

- **theories/session_logic/**  
  The session-typed program logic: session specifications, proof mode support,
  and linear constructs (telepresence, substructural operators, etc.).

- **theories/examples/**  
  Small example programs verified using the logic, such as:
  - `factorial.v`
  - `find.v`
  - `send_chan.v`
  - `send_recv.v`
  - `swap.v`
  - `multi_shot_closure.v`

- **theories/examples_la/**  
  Larger LinearActris examples, including:
  - `basics.v`
  - `assert.v`
  - `list_rev.v`
  - `llist.v`
  - `compare.v`
  - `prots.v`
  - `sort.v`
  - `sort_br_del.v`
  - `sort_fg.v`
  - `tour.v`

In addition to the main development:

- **stdpp/** — vendored copy of the std++ library.  
- **iris/** — vendored custom version of Iris.  
- Top-level `dune-project` file for building the project.
