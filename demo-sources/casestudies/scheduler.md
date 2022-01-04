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
  case Cons(hd, tl) => (reverse(tl), hd)
}}

// now we define the interface of our scheduler
interface Proc { def fork(): Boolean }

// and implement the scheduler itself
def schedule { p: { Proc } => Unit }: Unit {
  // "processes" spawned by fork are stored in this local mutable cell
  var q: List[() => Unit at {p, schedule}] = emptyQueue();

  // we run the program with our own scheduler
  try { p {proc} } with proc: Proc {
    // forking enqueues the continuation twice
    def fork() { q = enqueue(q, box { () => resume(true) });
                 q = enqueue(q, box { () => resume(false) }) }
  };

  // finally, while there are continuations, we dequeue and force them
  while (nonEmpty(q)) {
    dequeue(q) match {
      case (rest, k) =>
        // this "type-ascription" is necessary due to our preliminary
        // implementation of local type inference for matches
        val k2: () => Unit at {p, schedule} = k;
        q = rest;

        // force the continuation
        (unbox k2)()
    }
  }
}


// Example using the scheduler
interface Exc { def abort(): Unit }
def example() {
  try {
    schedule { {p:Proc} =>
      if (p.fork()) {
        println("(1)");
        if (p.fork()) {
          println("(2)"); exc.abort()
        } else { println("(3)") }
      } else { println("(4)") }
    }
  } with exc: Exc { def abort() { println("aborted") }}
}
```
Note how the use of local mutable state is safely encapsulated in function `schedule`, which does not close over anything.
We can run the above example, which forks two threads and aborts with an outer capability:

```effekt:repl
example()
```

Here, `schedule` takes in a program which expects a given `Proc` capability.  As this program
is a second-class argument, it can use additional capabilities that are not reflected in its type
(but are on its binder) due to System C's contextual effect polymorphism.  In particular,
these capabilities may be captured on the continuation term `resume`.  However, as those capabilities
are second class, they cannot leak through the resumption and the entire program is safe --
in particular, the resumption cannot leak even though it is stored in the mutable cell `q`, as
`q` is second-class itself and valid only within the context of the `scheduler` region.

In the example above, calling `exc.abort()` not only terminates one "thread", but the scheduler as a whole.
This is the expected behavior: The handler for exceptions is located _outside_ of the scheduler and thus the continuation captured and discarded by `abort` also includes the scheduler itself.