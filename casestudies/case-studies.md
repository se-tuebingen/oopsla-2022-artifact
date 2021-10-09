---
layout: default
title: Case Studies
nav_order: 4
has_children: true
permalink: /casestudies
---

# Case Studies

Reasoning about the use of external resources is an important aspect of many practical applications.
Examples range from memory management, controlling access to privileged
resources like file handles or network,
to analysing the potential presence or absence of side effects.



```effekt
interface Console {
  def println[A](a: A): Unit

}
interface Time {
  def now(): Int
}

def testModule { console: Console } { time: Time } {

  def foo() {
    console.println("test");
    ()
  }

  def sayHello() { console.println("Hello!") }
  def currentTime() { time.now() }
  def sayTime() { console.println("The current time is: " ++ show(time.now())) }

  def repeat(n: Int) { f: () => Unit }: Unit { f() }

  def repeater { f: () => Unit }: (Int) => Unit at { f } {
    box { (n: Int) => repeat(n) {f} }
  }

  val b = sayTime;

  val n = repeater { () => sayTime() };
  val n1 = repeater { sayTime };
  val b2 : () => Unit at {console, time} = box { () => (unbox n)(3) };
  val b3 = n(3);
  val b4 = { () => n(3) };

  def even() { console.println("hello"); odd() }
  def odd(): Unit { even() }

  val r = repeater { b };

  def race(fst: () => Unit at {}, snd: () => Unit at {}): Unit { () }

  // race(
  //     box { () => console.println("hello") },
  //     box { () => console.println("world") });

  ()
}

def main() { () }
```

### Effect Systems encourage type-based reasoning
They extend the static guarantees of type systems to additionally track the use
of effects. To do so, effect systems typically augment the type of functions with
information about which effects the function might use.
Effect systems have been successfully applied to all of the above-mentioned domains and more.
A practical example of an effect system are checked exceptions in Java were signatures
contain information about which exceptions a method might throw (use).
From a programmer's perspective, however, effect systems usually have a number of drawbacks
which inhibit a more widespread adoption.
In particular, the fundamental idea of enhancing types with additional
information is also one of the biggest problems of effect systems. Types quickly
become verbose, difficult to understand, and difficult to reason about -- especially in the presence of
effect-polymorphic higher-order functions [@zhang2016accepting;@rytz2012lightweight;@brachthaeuser2020effects].
In consequence, programmers avoid effect systems and some modern languages, such as Scala,
intentionally avoided adding one. After all, side-effects are only one problem and they should not hinder other
software design concerns.

### Capabilities encourage scope-based reasoning
They offer an alternative way to control the way resources are used.
In this model, one can access resources and effects only through capabilities.
Thus, restricting access to capabilities
restricts effects: a program can only perform
effects of capabilities it can use. Some capabilities have a limited
lifetime and should not leave a particular scope -- for instance,
if they are used to emulate checked exceptions. In these cases, type-based escape
analysis [@hannan1998escape] provides such static
guarantees. One particular system is based on _second-class_ values,
which can freely be passed as arguments, but never returned [@osvald2016gentrification].
From a language designer's perspective, capabilities and second-class values offer
an interesting alternative to effect systems:
programmers can reason about effects the same way they reason about bindings.
Additionally, second-class values admit a lightweight form of effect
polymorphism without extending the language with effect variables
or effect abstraction [@brachthaeuser2020effects].
While lightweight, such systems severely restrict expressivity.

### Comonadic type systems enable transitioning between type-based and scope-based reasoning
They have been designed allow programmers to reason about _purity_ in an impure
languages [@choudhury2020recovering].
A special type constructor `Safe a` witnesses the fact that its values
are constructed without using any (impure) capabilities. Values of type
`Safe a` are introduced and eliminated with special language constructs.
Importantly, explicit box introduction and elimination marks the transition
between reasoning about effects by which capabilities are currently in scope, and
reasoning about effects by types that witness the potential use of capabilities (that is, _impurity_).
The type system presented by @choudhury2020recovering only supports a binary
notion of _pure_ values and _impure_ values, which is not fine-grained enough for many practical
applications -- for instance, _effect masking_, or local handling of effects.

## This Paper

In this paper, we draw inspiration from all three lines of research
and present a calculus &core; that aims at striking the balance between
expressivity and simplicity. In particular, we combine and generalize the work by
@osvald2016gentrification and @choudhury2020recovering to obtain a
lightweight, capability-based alternative to effect systems.
&core; is based on the following design decisions:


#### Second-class Values
  Following @osvald2016gentrification, we distinguish between functions that
  can be treated as first-class values, and functions that are second-class.
  (To highlight this difference, we explicitly refer to second-class functions as _blocks_.)
  Thus, we avoid confronting programmers with the ceremony associated
  with tracking capabilities in types as much as possible.
  In particular, blocks can freely close over capabilities and effectful computations can simply use all capabilities
  in their lexical scope, with no visible type-level machinery to keep track of either fact.

#### Capability Sets
 Based on the work by !@osvald2016gentrification
  we annotate each binding in the typing context with additional information.
  However, we do not only track whether a bound variable is first- or second-class, but
  also track over _which capabilities_ it closes. That is, we
  augment bindings (&eg;, $f:^{C} s$) in the typing context with _capability sets_ (&eg; $C$).
  This information is annotated at the binder and _not_ part of the type.
  We will see that this is important for ergonomics as users are never confronted with this information.
  It is only necessary to check and guarantee effect safety.

#### Boxes
Blocks can freely close over other capabilities. However, they
  cannot be returned from a function or stored in a field.
  To recover these abilities we generalize the work by @choudhury2020recovering:
  &core; features explicit boxing and unboxing language constructs. Boxing
  converts a second-class value to a first-class value,
  reifying the contextual information annotated on the binder into the boxed
  value's type (&eg;, $f:^C s |- box f :: s at C$). That is, instead of completely preventing
  first-class values from closing over capabilities, the capabilities they closed over
  are tracked in their types.
  To use a boxed block, we have to unbox it. We make sure to only perform
  this operation when the capabilities (&eg;, $C$) are still in scope,
  which guarantees effect safety. The $box$ and $unbox$ constructs allow programmers to freely
  move between tracking capabilities implicitly, via scope, or explicitly, via type.

## Contributions and Overview
This paper makes the following contributions:

- An example driven introduction to programming with capabilities in &core;, a calculus that
  reconciles scope-based and type-based reasoning in a language with advanced control effects (Section [#sec-motivation]).
- A formal presentation of &core; with static and dynamic semantics (Section [#section-formalism]).
  The typing context in &core; is enhanced with additional information about block binders,
  which only becomes visible in types when explicitly boxing blocks.
- A proof of progress and preservation (Theorems [#th-progress] and [#th-preservation]),
  as well as effect safety (Corollary [#th-effect-safety]).
- A full mechanization of the calculus, as well as proofs of the progress and preservation
  in the Coq theorem prover (Section [#section-mechanization]).
- An extension to the &lang; language [@brachthaeuser2020effects] with first-class functions, internally using &core; as an intermediate representation (Section [#sec-discussion]). We submit an executable translation of all examples from this paper to &lang; as supplementary material.
