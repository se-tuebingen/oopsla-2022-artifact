---
layout: default
title: Paper Examples
nav_order: 4
has_children: true
permalink: /paper
---

## Examples from the Paper
```effekt
import immutable/list
def emptyQueue[T]() { Nil[T]() }
def enqueue[T](q: List[T], el: T): List[T] { Cons(el, q) }
def nonEmpty[T](q: List[T]) { size(q) > 0 }
def dequeue[T](q: List[T]) { reverse(q) match {
  case Nil() => panic[(List[T], T)]("Empty queue")
  case Cons(hd, tl) => (tl, hd)
}}
```

```effekt
import immutable/list
interface Proc { def fork(): Boolean }
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