---
layout: default
title: Section 4
parent: Paper Examples
nav_order: 3
---

## Section 4.2 -- Mutable State
```effekt
interface State[S] {
  def get(): S
  def set(v: S): Unit
}
def handleState[S, R](init: S) { prog: {State[S]} => R }: R {
  val stateFun: S => R at {prog} =
    try { val res = prog { state }; return box {prog} { (s: S) => res } }
    with state: State[S] {
      def get() { box { (s: S) => (unbox resume(s))(s) } }
      def set(v: S) { box { (_: S) => (unbox resume(()))(v) } }
    };
  return (unbox stateFun)(init)
}
```
```effekt:repl
handleState(0) { {s: State[Int]} => println(s.get()); s.set(2); println(s.get()) }
```

For more details on regions, also see the corresponding [regions case study](regions).
```effekt
def regions1() {
  region r {
    var x in r = 42;
    val t = x;
    x = (t + 1)
  }
}
```
```effekt
def regions2() {
  region r {
    var x in r = 42;
    val f: () => Int at {r} = box { () => x };
    (unbox f)()
  }
}
```
```effekt:repl
regions2()
```

## Example 4.1
A quick draft of queues using lists.
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

## Section 4.4 -- Effect Handlers and Object Orientation
Similar examples can be found in the [regions case study](/casestudies/regions.html#regions).

Support code to run the example from Section 2.
```effekt
interface Console { def println[A](a: A): Unit }
def run[T] { prog : {Console} => T }: T {
  try {
    prog {console}
  } with console: Console {
    def println[A](msg: A) { println(msg); resume(()) }
  }
}
```


```effekt
interface Counter {
  def inc(): Unit
  def get(): Int
}
def counterExample { console: Console }: Unit {
  def makeCounter { pool: Region }: Counter at {pool, console} {
    var count in pool = 0;
    def c = new Counter {
      def inc() { console.println(count); count = count + 1 }
      def get() { count }
    };
    return box c
  }

  region r {
    val c1 = makeCounter {r};
    val c2 = makeCounter {r};

    c1.inc();
    c1.inc();
    c2.inc();
    console.println(c1.get());
    console.println(c2.get())
  }
}
```

```effekt:repl
run {counterExample}
```