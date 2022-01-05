---
layout: default
title: Proofs
has_children: true
nav_order: 2
---

# Proofs

> *Copyright Notice* The proofs were based on an existing proof of [System-F-Sub in locally nameless](http://www.chargueraud.org/softs/ln/) by Brian Aydemir and Arthur Charguéraud, Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis. While the definitions heavily changed, the infrastructure code regarding bindings is still very similar.

#### Proof Sources
The documentation on this page is automatically generated from Coq proof files. The files can be found in the github repository of this artifact:

> <{{site.github}}/tree/main/coq>

Not all proof-files are equally well documented.
For the artifact, we carefully prepared the following files, which we recommend to look at.

## Definitions of Syntax, Typing, and Semantics
In file [Definitions](Top.SystemC.Definitions.html), you can inspect the Coq definitions and compare them with the paper's definition.

## Main Theorems
File [Soundness](Top.SystemC.Soundness.html) lists the main theorems, like progress and preservation. File [Substitution](Top.SystemC.Substitution.html) contains lemmas about context weakening as well as the standard substitution lemmas.
