# Step-By-Step

We will make our artifacts available via Zenodo.

We provide two artifacts: a mechanized proof of soundness and an implementation of System C.

## Claims supported by the artifact

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
explain the differences in the above pages as necessary.

Our implementation is also slightly stronger than the exact calculus we present
in the paper, as it supports type polymorphism.

## Implementation

Our implementation shows that...

TODO: well, what does it actually show?
- capabilities can be hidden from the user and inferred by the type system
- wasn't it also supposed to show that System C is pragmatic/simple/usable? Do
  we claim that in the paper?
- ...

As we point out in the paper (Section 4), our implementation of System C extends
the formal calculus with type polymorphism, mutable state and objects.

## Suggested Steps for Evaluation

1. We suggest to familiarize yourself with [the interactive implemention](https://se-tuebingen.github.io/oopsla-2022-artifact/).
2. The examples in the paper can be found in [the examples section](https://se-tuebingen.github.io/oopsla-2022-artifact/paper.html).

The snippets with the examples are interactive -- they can be typechecked and
edited, and, if it makes sense, ran. Note that examples not expressed in System
C cannot be found on the website. The exact examples we presented in our paper
are sometimes surrounded by additional code in order to make the entire snippet
self-contained; this is explicitly pointed out next to the appropriate snippets
and explained on this page.

TODO: modify the examples as explained above.
