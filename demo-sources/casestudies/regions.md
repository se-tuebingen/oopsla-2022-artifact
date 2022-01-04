---
layout: default
title: Region-based Local State
parent: Case Studies
nav_order: 2
---

## Local Backtrackable State
Since System C features effect handlers and multiple resumptions, mutable state needs to be used with care.
Take the following standard handler for ambiguity that runs explores all possible choices.

```effekt
interface Amb { def flip(): Boolean }

def allChoices { prog : {Amb} => Unit }: Unit {
  try { prog {amb} } with amb: Amb {
    def flip() { resume(true); resume(false) }
  }
}
```

If we declare the mutable variable _outside_ of the handler for ambiguity, changes should be persisted across different explored alternatives:
```effekt
def stateExample1() {
  var x = 1;
  allChoices { {amb: Amb} =>
    if (amb.flip()) { x = 2 } else { () };
    println(x)
  }
}
```

```effekt:repl
stateExample1()
```
whereas, if we declare the mutable variable within the handler for ambiguity, it should perform backtracking:
```effekt
def stateExample2() {
  allChoices { {amb: Amb} =>
    var x = 1;
    if (amb.flip()) { x = 2 } else { () };
    println(x)
  }
}
```

```effekt:repl
stateExample2()
```

In order to achieve this correct backtracking behaviour, state is allocated on the stack, captured together with the continuation and restored on resumption.

## Regions

In fact, all local mutable variables are allocated in corresponding regions. The regions become visible, when trying to close over the references:
```effekt
def stateExample1b() {
  var x = 1;
  val closure = box { () => x };
  ()
}
```
The inferred capability set for `closure` is `{stateExample1b}`. This illustrates that `x` is allocated in a region associated with the current function definition. We could also make this more explicit as:

```effekt
def stateExample1c() {
  region r {
    var x in r = 1;
    val closure = box { () => x };
    ()
  }
}
```
Now, the inferred capability set at `closure` is `{r}`. Regions are second-class and can be passed to functions:

```effekt
def newCounter {pool: Region} {
  var state in pool = 0;
  return box { () => println(state); state = state + 1 }
}
```
Hovering over `newCounter`, we can see that the inferred return type is `() => Unit at {pool}`. That is, we return a function that closes over the region that we passed to it.

Let us allocate a fresh region and use the above defined function:
```effekt
def stateExample3() {
  region pool {
    val c1 = newCounter {pool};
    val c2 = newCounter {pool};

    c1();
    c1();
    c2();
    c1();
    c2()
  }
}
```
```effekt:repl
stateExample3()
```

## Backtrackable Regions
Of course the two concepts can be combined and regions show the correct backtracking behavior.

```effekt
def exampleProgram {amb:Amb} {reg:Region} {
  var x in reg = 1;
  if (amb.flip()) { x = 2 } else { () };
  println(x)
}

def stateExample4() {
  region pool {
    allChoices { {amb: Amb} =>
      exampleProgram {amb} {pool}
    }
  }
}
```
```effekt:repl
stateExample4()
```
and nested the other way around:
```effekt
def stateExample5() {
  allChoices { {amb: Amb} =>
    region pool {
      exampleProgram {amb} {pool}
    }
  }
}
```
```effekt:repl
stateExample5()
```