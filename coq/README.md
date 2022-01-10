# System C Proofs

This project contains the Coq proofs for System C.
We developed the proofs with

    Coq version 8.10.2


A makefile is attached, but to recreate it in case of problems, run the following command:

    coq_makefile -f _CoqProject -o Makefile.coq

Then, to actually build the proofs:

    make

## Evaluation

We recommend inspecting file `SystemC.Definitions.v` in the rendered documentation, which
contains a detailed overview of similarities and differences to the paper.

## Proof Structure

The proofs are based on the POPL'08 locally-nameless proof of System F(-sub).

- All definitions can be found in the file `SystemC.Definitions.v`.
- The files `SystemC.Infrastructure.v` and `SystemC.Lemmas.v` contain technical lemmas related to
  locally nameless and wellformedness.
- File `SystemC.Substition.v` contains lemmas concerning typing under term and type substitution.
- The file `SystemC.Soundness.v` contains lemmas leading to and including preservation and progress.
- Finally, the file `SystemC.Examples.v` contains proofs of typing and reduction for a selected
  sample set of terms written in System-C, including terms analogous to examples presented in the paper.
  The file includes a description of the examples.
