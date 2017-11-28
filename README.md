OOlong
======

This repository contains the Ott and Coq sources for OOlong, a
concurrent object calculus for modelling object-oriented
languages. The calculus was first presented in the article
"OOlong: An Extensible Concurrent Object Calculus" (link
forthcoming).

This repository will be further updated as soon as I have finished
writing my thesis =)

The structure of this directory is as follows:

* `ott` contains the Ott sources for OOlong and a sample LaTeX
  file that uses the generated type rules. It also contains our
  hand written LaTeX code for the more compact syntax of OOlong.
  There is a makefile which builds the sample document. Ott can be
  installed from here: http://www.cl.cam.ac.uk/~pes20/ott/

* `coq` contains the mechanised semantics of OOlong, both the
  "vanilla" version from the paper, and the two extensions brought
  up in section 8.