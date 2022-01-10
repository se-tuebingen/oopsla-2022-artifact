# Step-By-Step

We provide two artifacts that support the claims made in the paper: a mechanized proof of soundness and 
an implementation of System C.

Here, we describe in more detail, how the artifacts support the claims.

## Coq Proofs: Claims supported by the artifact

In Section 1.5, we claim to provide

> A full mechanization of the calculus, as well as proofs of the progress and preservation in
the Coq theorem prover (Section 3.5.4).

This mechanization can be found in the folder `coq`. We wrote a detailed
guide on how the proofs correspond to the paper, which can be found at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/>

### Definitions

We propose the reviewers visit the documentation of the 
[Coq Definitions](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html)
and compare them with the paper.

### Theorems

In Section 3, we claim that System C satisfies standard Progress and
Preservation theorems.

These claims correspond to the following definitions in our mechanization:

- Theorem 3.2 - [Preservation](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#preservation).
- Theorem 3.4 - [Progress](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#progress).
- Lemma 3.5 - [styping_through_subst_cs](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Substitution.html#substitution).
- Lemma 3.6 - [unwind_step](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Soundness.html#unwind_step).

We also present Lemma 3.3, which is proven in the paper, in Appendix A.3.
In the mechanization, we instead require that Lemma 3.3 holds by [definition](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html#stacks).
  
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

> An evaluation in terms of an **implementation** (Section 4) and several **small case studies**.

We submit this implementation, an executable version of **all System C examples
from this paper** and the case studies as supplementary material.

The implementation is provided in terms of an interactive website:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/index.html>

All examples from the paper can be found at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/paper.html>
  
The additional case studies are located at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/casestudies.html>

Footnote 3, page 5 we claim (paraphrasing):

> The capture sets highlighted in blue are inferred by the type checker and displayed by the IDE.

Footnote 4, page 6 we claim:

> In our implementation of System C, we infer almost all necessary boxing and unboxing operations. However, in the paper, for exposition we refrain from doing so.

The examples we provide are interactive - they can be typechecked, edited and
ran. Similar to the paper, in our IDE implementation, inferred capture sets are highlighted in blue.
That is, typechecking the examples (and inferring capture sets) will indeed display capture sets corresponding to the ones from the paper.
Moreover, in almost all the cases, removing explicit `box` and `unbox` from the examples will keep them typecheckable.

As we point out in the paper (Section 4), our implementation of System C extends
the formal calculus with type polymorphism, mutable state, and objects. Mutable state is illustrated in an additional [case study](https://se-tuebingen.github.io/oopsla-2022-artifact/casestudies/regions.html).

### Suggested Steps for Evaluation

We suggest that the reviewers:
1. Familiarize themselves with [the interactive implemention](https://se-tuebingen.github.io/oopsla-2022-artifact/).
2. Inspect [the examples section](https://se-tuebingen.github.io/oopsla-2022-artifact/paper.html),
   which contains examples from the paper. To verify that we indeed infer the capture sets we claim to infer, we suggest
   typechecking Example 2.1 from [Section 2](https://se-tuebingen.github.io/oopsla-2022-artifact/paper/section2.html#example-21).
   To verify that we infer `box`/`unbox` operations, we suggest removing either or both keywords in the above example and
   re-typechecking it. We then suggest replacing `fileA` with `fileB` on the line that originally contained `return box`,
   to verify that we indeed reject ill-typed examples.
3. Inspect [the case studies](https://se-tuebingen.github.io/oopsla-2022-artifact/casestudies.html),
   verifying that they type check and run.
