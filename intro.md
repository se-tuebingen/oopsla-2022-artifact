---
layout: page
title: Basics
permalink: /intro/
nav_order: 1
---

# Basics
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

You can try it out!
```effekt:repl
println(Red())
```

As usual, datatypes can also take type parameteres and be recursive:
```effekt
type Pair[A, B] {
  Pair(fst: A, snd: B)
}

type List[A] {
  Cons(head: A, tail: List[A])
  Nil()
}
```

Datatypes can be destructed using pattern matching:
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
  // this is shorthand for Cons(1, Cons(2, Cons(3, Nil())))
  val l = [1, 2, 3];
  val z1 = l match {
    case Nil() => 0
    case Cons(x, tl) => x + 1
  };
  println(z1);
  ()
}
```

```effekt:repl
doPair()
```