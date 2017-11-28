This directory contains the Coq sources of the mechanised
semantics of OOlong. `vanilla` contains the semantics as presented
in the paper. `assert` and `region` contains the variations
brought up in section 8 of "OOlong: An Extensible Concurrent
Object Calculus".

The structure of the Coq code is the same for all versions. For
each file `Foo.v` containing definitions, there is a `FooProp.v`
containing lemmas (with proofs) of properties of the constructs
from `Foo.v`. These are the different modules in each project:

* `Meta` defines all meta-syntactic variables (mostly
  represented as `nat`) and the functionality for partial maps.

* `Syntax` defines the syntax of OOlong, including both static
  and dynamic constructs.

* `Types` defines the static semantics of types and expressions,
  including subtyping.

* `Wellformedness` defines the well-formedness rules for both
  static and dynamic constructs.

* `Dynamic` defines the dynamic semantics of OOlong.

* `Locking` defines lemmas related to locking behaviour.

* `Progress` contains the proof of progress.

* `Preservation` contains the proof of preservation.

* `Soundness` proves type soundness using progress and
  preservation.

* `Shared` contains general tactics, including the Case library.

* `ListExtras` contains auxilary lemmas about lists.

* `CpdtTactics` contains the `crush` tactic by Adam Chlipala.

* `LibTactics` contains the `LibTactics` library from Software
  foundations.

Each version has a makefile to build the project from scratch.