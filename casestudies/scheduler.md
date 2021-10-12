---
layout: default
title: Scheduling (with continuations and mutable cells)
parent: Case Studies
nav_order: 2
---
## Scheduling Tasks and Continuations

Writing a safe, co-operatively threaded scheduler in an effect safe manner can be hard, as it requires treating continuations
as first-class values.
Continuations might indirectly close over other capabilities and we want to prevent that capabilities leave their defining scope indirectly through continuations.
System C can safely express this though -- the following is a skeleton of a scheduler.

```effekt
import immutable/list

// we first draft a naive implementation of a queue
def emptyQueue[T]() { Nil[T]() }
def enqueue[T](q: List[T], el: T): List[T] { Cons(el, q) }
def nonEmpty[T](q: List[T]) { size(q) > 0 }
def dequeue[T](q: List[T]) { reverse(q) match {
  case Nil() => panic[(List[T], T)]("Empty queue")
  case Cons(hd, tl) => (tl, hd)
}}

def schedule { p: { Proc } => Unit }: Unit {
  var q: List[() => Unit at {p, schedule}] = emptyQueue();
  try { p {proc} } with proc: Proc {
    def fork() { q = enqueue(q, box { () => resume(true) });
                 q = enqueue(q, box { () => resume(false) }) }
  };
  while (nonEmpty(q)) {
    dequeue(q) match {
      case (q2, k) =>
        val k2: () => Unit at {p, schedule} = k;
        q = q2;
        (unbox k2)()
    }
  }
}
```
For example, we can use the above defined handler to fork two threads:
```effekt
def schedulerExample() {
  schedule { {p:Proc} =>
    if (p.fork()) {
      println("(1)");
      if (p.fork()) {
        println("(2)")
      } else { println("(3)") }
    } else { println("(4)") }
  }
}
```
```effekt:repl
schedulerExample()
```

Here, `schedule` takes in a program which expects a given `Proc` capability.  As this program
is a second-class argument, it can use additional capabilities that are not reflected in its type
(but are on its binder) due to System C's contextual effect polymorphism.  In particular,
these capabilities may be captured on the continuation term `resume`.  However, as those capabilities
are second class, they cannot leak through the resumption continuation and the entire program is safe --
in particular, the resumption cannot leak even though it is stored in the mutable cell `q`, as
`q` is valid only within the context of the `scheduler` region.