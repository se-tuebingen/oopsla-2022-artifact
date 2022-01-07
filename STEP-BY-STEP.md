# Step-By-Step

> **Availability**: We will make our artifacts available via Zenodo.

We provide two artifacts that support the claims made in the paper: a mechanized proof of soundness and 
an implementation of System C.

The [GETTING-STARTED.md](./GETTING-STARTED.md) guide explains how to set up each of the 
two artifacts. Here, we describe in more detail, how the artifacts support the claims.

## Coq Proofs: Claims supported by the artifact

In Section 1.5, we claim to provide

> A full mechanization of the calculus, as well as proofs of the progress and preservation in
the Coq theorem prover (Section 3.5.4).

This mechanization can be found in the folder [coq](./coq). We wrote a detailed
guide on how the proofs correspond to the paper, which can be found at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/>

### Definitions

We propose the reviewers visit the documentation of the [Coq Definitions](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html) and compare them with the paper.

### Theorems

In Section 3, we claim that System C satisfies standard Progress and
Preservation theorems (respectively Theorem 3.2 and 3.4), as well as Lemma 3.6,
an additional continuation safety lemma.

These claims correspond to the following definitions in our mechanization:
- Lemma 3.6 - [unwind_step](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#unwind_step)
- Theorem 3.2 - [Preservation](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#preservation)
- Theorem 3.4 - [Progress](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#progress)

TODO: link more theorems.
  
Note that our mechanization uses abstract machine semantics, as we explained in
the paper and detailed in Appendix A.4. This means that the mechanized
statements of theorems and lemmas differ slightly from those in the paper. We
explain the differences in the above pages as necessary. The definition of the
abstract machine in Coq is documented at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html#abstract-machine>

Our implementation is also slightly stronger than the exact calculus we present
in the paper, as it supports type polymorphism.

## Implementation

In Section 1.5, we claim to provide...

> An evaluation in terms of an **implementation** (Section 4) and several **small case studies**. We
submit an executable version of all **examples from this paper** as supplementary material.

The implementation is provided in terms of an interactive website,

  <https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/index.html>

all examples from the paper can be found at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/paper.html>
  
and the additional case studies are located at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/casestudies.html>

Our implementation shows that...

TODO: well, what does it actually show?
- capabilities can be hidden from the user and inferred by the type system
- wasn't it also supposed to show that System C is pragmatic/simple/usable? Do
  we claim that in the paper?
- ...

As we point out in the paper (Section 4), our implementation of System C extends
the formal calculus with type polymorphism, mutable state and objects.

TODO

Footnote 4, page 6 we claim:

> In our implementation of System C, we infer almost all necessary boxing and unboxing operations. However, in the paper, for exposition we refrain from doing so

TODO

### Suggested Steps for Evaluation

1. We suggest to familiarize yourself with [the interactive implemention](https://se-tuebingen.github.io/oopsla-2022-artifact/).
2. The examples in the paper can be found in [the examples section](https://se-tuebingen.github.io/oopsla-2022-artifact/paper.html).

The snippets with the examples are interactive -- they can be typechecked and
edited, and, if it makes sense, ran. Note that examples not expressed in System
C cannot be found on the website. The exact examples we presented in our paper
are sometimes surrounded by additional code in order to make the entire snippet
self-contained; this is explicitly pointed out next to the appropriate snippets
and explained on this page.

TODO: modify the examples as explained above.
