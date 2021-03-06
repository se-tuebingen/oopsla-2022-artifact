# Artifact for the OOPSLA 2022 paper 'Effects, Capabilities, and Boxes'

[![DOI](https://zenodo.org/badge/412428588.svg)](https://zenodo.org/badge/latestdoi/412428588)

This github repository constitutes the artifact for our paper

> Effects, Capabilities, and Boxes: From Scope-based Reasoning to Type-based Reasoning and Back.
> Jonathan Immanuel Brachthäuser, Philipp Schuster, Edward Lee, Aleksander Boruch-Gruszecki.
> Conditionally accepteed at OOPSLA 2022.

## Overview

The artifact consists of two parts:

1. [`coq/`](./coq/): Coq proofs, proving soundness of the calculus System C
2. [`demo-sources/`](./demo-sources/): A website featuring an implementation of System C with examples that can be typechecked, edited, and run.

While the repository contains the sources of the website (and for archival purposes we submit the built website as a compressed archive), we do not propose to
build the website yourself. Instead, we use github-pages (branch [`gh-pages`](https://github.com/se-tuebingen/oopsla-2022-artifact/tree/gh-pages)) to host the artifact, which is made available at:

  <https://se-tuebingen.github.io/oopsla-2022-artifact/>

The website contains

- [Documentation of the proofs](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/), with [detailed information](https://se-tuebingen.github.io/oopsla-2022-artifact/proofs/Top.SystemC.Definitions.html) on how the Coq mechanization corresponds to the calculus as it is presented in the paper.

- [An executable implementation](https://se-tuebingen.github.io/oopsla-2022-artifact/tutorial/) of the calculus. 

We claim reusability of the proofs and the interactive demo, but not of the calculus _implementation_ itself.

### Additional Instructions
Please find additional instructions in the following two files:

- [`GETTING-STARTED.md`](./GETTING-STARTED.md) for the kick-the-tires phase.
- [`STEP-BY-STEP.md`](./STEP-BY-STEP.md) for suggestions on how to proceed with the evaluation of the artifact.
