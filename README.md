OOlong
======

This repository contains the Ott, Coq and OCaml sources for
OOlong, a concurrent object calculus for modelling object-oriented
languages. The calculus was first presented in the article
"OOlong: An Extensible Concurrent Object Calculus" (link
forthcoming). An extended version of the paper also explaining the
OCaml interpreter is under submission.

The structure of this directory is as follows:

* `ott` contains the Ott sources for OOlong and a sample LaTeX
  file that uses the generated type rules. It also contains our
  hand written LaTeX code for the more compact syntax of OOlong.
  There is a makefile which builds the sample document. Ott can be
  installed from here: http://www.cl.cam.ac.uk/~pes20/ott/

* `coq` contains the mechanised semantics of OOlong, both the
  "vanilla" version from the paper, and the two extensions brought
  up in section 8. "nullable" is explained in the extended
  version, which will be available soon.

* `ocaml` contains a prototype interpreter for OOlong. It is
  written to have a simple _implementation_, and to allow type
  checking and running OOlong programs. It is not meant to be
  efficient (and error reporting could use some work). See also
  the branch `arith`, which adds integers and addition.