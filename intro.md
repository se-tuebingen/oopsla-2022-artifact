---
layout: page
title: Basics
permalink: /intro/
nav_order: 1
---


System C supports basic datatypes, such as numbers, strings, functions, and booleans.
```effekt
def hello(): Unit {
    val one = 1;
    val hello = "Hello";
    val check = true;
    println(hello)
}
```

In addition to these basic datatypes, it also has support for inductive
datatypes; for example:
```effekt
    type Color { Red() Green() Blue() }
```

Try it out!
```effekt:repl
    println(Red())
```

A more complicated datatype:
```effekt
type Pair[A, B] {
  Pair(fst: A, snd: B)
}

type List[A] {
  Cons(head: A, tail: List[A])
  Nil()
}
```

And a function which pattern-matches on it:
```effekt
def doPair() {
  Pair(1, 2) match {
    case Pair(x, y) => println(x + y)
  };
  val z = Pair(Pair(1, 2), 3) match {
    case Pair(Pair(x, y), z) =>
      x + y + z
  };
  println(z);
  val z1 = [1, 2, 3] match {
    case Nil() => 0
    case Cons(x, tl) => x + 1
  };
  println(z1);
  ()
}
```

Try it out!
```effekt:repl
doPair()
```