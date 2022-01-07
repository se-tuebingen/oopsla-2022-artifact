---
layout: default
title: Section 4
parent: Paper Examples
nav_order: 3
---

## Section 4.2 -- Mutable State
```effekt
// PREAMBLE
interface State[S] {
  def get(): S
  def set(v: S): Unit
}
// EXAMPLE
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
handleState(0) { {s: State[Int]} =>
  println(s.get());
  s.set(2);
  println(s.get());
}
```

For more details on regions, also see the corresponding [regions case study](../casestudies/regions.html).
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
See the [scheduler case study](.../casestudies/scheduler.html)

## Section 4.4 -- Effect Handlers and Object Orientation
Similar examples can be found in the [regions case study](../casestudies/regions.html#regions).

The definition below allows running the examples.

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
// PREAMBLE
interface Counter {
  def inc(): Unit
  def get(): Int
}
def counterExample { console: Console }: Unit {
// EXAMPLE
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
// POSTAMBLE
}
```

```effekt:repl
run {counterExample}
```
