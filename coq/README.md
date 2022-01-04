# System C Proofs

This project contains the Coq proofs for System C.
We developed the proofs with Coq version 8.10.2.


A makefile is attached, but to recreate it in case of problems, run the following command:

    coq_makefile -f _CoqProject -o Makefile

Then, to actually build the proofs:

    make

## Overview

The proofs are based on the POPL'08 locally-nameless proof of System F(-sub). We recommend looking into `Rho_Examples.v` for examples and `Rho_Definitions.v` for definitions. We renamed our calculus at some point from "Rho" to "System C". While the filenames still carry the old name, the proofs are up-to-date.

- All definitions can be found in the file `Rho_Definitions.v`.
- The files `Rho_Infrastructure.v` and `Rho_Lemmas.v` contain technical lemmas related to type
  regularity and substitution.
- File `Rho_Substition.v` contains lemmas concerning typing under term and type substitution.
- The file `Rho_Soundness.v` contains lemmas leading to and including preservation and progress.
- Finally, the file `Rho_Examples.v` contains proofs of typing and reduction for a selected
  sample set of terms written in System-C, including terms analogous to examples presented in the paper. The file includes a description of the examples.
