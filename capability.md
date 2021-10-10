---
layout: page
title: Capabilities
permalink: /capability/
nav_order: 2
---

# Capabilities and Effects

## Interfaces
Capability (and effect) types in System C are introduced with the `interface`
keyword.  For example, the following introduces the capability type `Greeter`
which has an operation `sayHello` associated with it.
```effekt
interface Greeter {
  def sayHello(): Unit
}
```

To use it, we can require an instance of the `Greeter` capability type:
```effekt
def useGreeter { g: Greeter } {
  g.sayHello()
}
```
Notice how interfaces and capabilities are _block types_ enclosed in curly braces. They are second-class.

Finally, to actually call `useGreeter`, we need to handle it with
a concrete handler which implements the `Greeter` interface and produces
an concrete instance of the `Greeter` interface:
```effekt
def myGreeter() {
  try {
    useGreeter {greeter}
  } with greeter: Greeter {
    def sayHello() {
      println("Hello World!");
      resume(())
    }
  }
}
```
System C features effect handlers:
after printing `"Hello World"`, we resume evaluation at the point of the call to `sayHello`.

```effekt:repl
myGreeter()
```

### Side-Effects
While capabilities can be used to precisely track side effects, in our draft implementation we chose to expose the (unsafe) builtin function `println`, which is not tracked. We can simply track access to the console by defining:
```effekt
interface Console { def println(msg: String): Unit }
def myFunction { console: Console } {
  console.println("hello");
  def nested() { console.println("world") }
  nested()
}
```
Type checking the example we can see that for `nested`, we infer a capability set of `{console}`.

## Using Multiple Effects and Capabilities
A capability type can have more than one operation, and these
operations can also return values; for example:
```effekt
interface Bank {
  def debit(amount: Int): Unit
  def credit(amount: Int): Unit
  def balance(): Int
}
```

Here is a small example which implements the `Bank` interface (perhaps not very well,
though, as it does nothing and your balance is always $0):
```effekt
def simpleAccount(): Unit {
  var balance = 0;
  try {
    bank.debit(10);
    bank.credit(5);
    println(bank.balance())
  } with bank: Bank {
    def debit(amount: Int) {
      balance = balance - amount;
      resume(())
    }
    def credit(amount: Int) {
      balance = balance + amount;
      resume(())
    }
    def balance() {
      resume(balance)
    }
  }
}
```

We can abstract over the handler for `Bank` and also add exceptions:

```effekt
interface AccountExc { def outOfMoney[A](): A }
def account[T] { exc: AccountExc } { prog: {Bank} => T } : T {
  var balance = 0;
  try { prog {bank} }
  with bank : Bank {
    def debit(amount : Int) {
      if (amount > balance) {
        exc.outOfMoney()
      } else {
        balance = balance - amount;
        resume(())
      }
    }
    def credit(amount : Int) {
      balance = balance + amount;
      resume(())
    }
    def balance() {
      resume(balance)
    }
  }
}

def userProgram(): Unit {
  try {
    account {exc} { {bank:Bank} =>
      bank.credit(10);
      bank.debit(5);
      println(bank.balance())
    }
  } with exc: AccountExc {
    def outOfMoney[A]() { println("Too bad.") }
  }
}
```
```effekt:repl
userProgram()
```

You can try changing the argument of `debit` from `5` to something larger then `10` and then rerun the program.

## Polymorphism through Second Class Capabilities
System C supports effect polymorphism through capability polymorphism.  For example,
here is a function which calls a second function which may perform some effectful operation.
```effekt
def invoke { f : () => Unit }: Unit { f() }

def useInvoke() {
  try {
    invoke { () => useGreeter {greeter} }
  } with greeter: Greeter {
    def sayHello() {
      println("Hello World from useInvoke!");
      resume(())
    }
  }
}
```

Contextual effect polymorphism means: In the block passed to `invoke`, we can simply use any capability that is lexically in scope.

```effekt:repl
useInvoke()
```

This seems unsafe -- what if `f` escaped?  However, it cannot, as by default, capabilities in
System C are _second class_ -- that is, they can only be passed as parameters and never returned.
Moreover, functions which close over second class capabilities have the capability recorded on their
binding, and by default, functions themselves are _second class_.
Syntatically, second-class (block) parameters are denoted by `{}` instead
of `()`.

```effekt
def otherInvoke() {
  try {
    // here inner closes over greeter, which is recorded on the binding
    def inner() {
      greeter.sayHello()
    }
    inner()
  } with greeter : Greeter {
    def sayHello() {
      println("Hello World from useInvoke!");
      resume(())
    }
  }
}

```

## Transparent wrapping and aliasing
Finally, capabilities and blocks can be bound to different names. However, our type system records which _tracked_ capabilities each block binder closes over, effectively performing some form of aliasing analysis.

For example, for aliased capabilities, we can bind `greeter` to `checker` but the
binding for `checker` still reflects the underlying bound capability:
```effekt
def boundInvoke() {
    try {
        def checker1 = greeter;
        def checker2 = { () => greeter.sayHello() };
        checker1.sayHello()
    } with greeter : Greeter {
        def sayHello() {
            println("Hello World from useInvoke!");
            resume(())
        }
    }
}
```
