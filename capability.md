---
layout: page
title: Capabilities
permalink: /capability/
nav_order: 2
---

# Capabilities and Effects

## An introduction
Capability (and effect) types in System C are introduced with the `interface`
keyword.  For example, the following introduces the capability type `Greeter`
which has an effectful operation `sayHello` associated with it.
```effekt
interface Greeter {
    def sayHello(): Unit
}
```

To use it, we just need an instance of the `Greeter` capability type:
```effekt
def useGreeter {g : Greeter} {
    g.sayHello()
}
```

Finally, to actually call `useGreeter`, we need to handle it with
a concrete handler which implements the `Greeter` interface and produces
an concrete instance of the `Greeter` interface:
```effekt
def myGreeter() {
    try {
        useGreeter {greeter}
    } with greeter : Greeter {
        def sayHello() {
            println("Hello World!");
            resume(())
        }
    }
}
```

Try it!
```effekt:repl
myGreeter()
```

## More complicated capabilities and effects
A capability type can have more than one effectful operation, and these
operations can also return values; for example:
```effekt
interface Bank {
    def debit(cash: Int) : Unit
    def credit(cash: Int) : Unit
    def balance() : Int
}
```

Here is a small example which implements the `Bank` interface (perhaps not very well,
though, as it does nothing and your balance is always $0):
```effekt
def myBadBank() {
    try {
        bank.debit(10);
        bank.credit(5);
        println(bank.balance())
    } with bank : Bank {
        def debit(cash : Int) {
            resume(())
        }
        def credit(cash : Int) { 
            resume(())
        }
        def balance() {
            resume(0)
        }
    }
}
```

## Polymorphism through Second Class Capabilities
System C supports effect polymorphism through capability polymorphism.  For example,
here is a function which calls a second function which may perform some effectful operation.
```effekt
def invoke {f : () => Unit} : Unit {
    f()
}

def useInvoke() {
    try {
        invoke {() => useGreeter {greeter}} 
    } with greeter : Greeter {
        def sayHello() {
            println("Hello World from useInvoke!");
            resume(())
        }
    }
}
```

Try it!
```effekt:repl
useInvoke()
```

This seems unsafe -- what if `f` escaped?  However, it cannot, as by default, capabilities in
System C are _second class_ -- that is, they can only be passed as parameters and never returned.
Moreover, functions which close over second class capabilities have the capability recorded on their
binding, and by default, functions themselves are _second class_.

```effekt
def otherInvoke() {
    try {
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