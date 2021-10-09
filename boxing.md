---
layout: page
title: Boxing and Unboxing
permalink: /boxing/
nav_order: 3
---
# Boxing and Unboxing

As we observed earlier, by default functions and capabilites are second class -- they cannot be returned nor stored in mutable cells and can only be passed as second-class parameters to other functions.  We can lift this
restriction by _boxing_ these functions and capabilities, reifying the set of captured capabilites from the binder to the type.

```
interface Greeter {
    def sayHello(): Unit
}

def myGreeter() {
    try {
        var capturedGreeter = greeter;
        val bar = {() => (unbox capturedGreeter).sayHello()};
        bar()
    } with greeter : Greeter {
        def sayHello() {
            println("Hello World!");
            resume(())
        }
    }
}
```

Here, we box `greeter` to store it in the mutable cell `capturedGreeter`.
While System C supports automatic boxing and unboxing, we could have
written the box explicitly by writing `box {greeter} greeter` or `box greeter`.  In addition, we implicitly box the function which invokes
`capturedGreeter.sayHello` and store it in bar.  Finally, we implictly
unbox `bar` to call it.

Boxed values act as normal first-class values in System C until unboxed.
In particular, they can be passed as values to value-polymorphic functions.
```effekt
def invoke[T](v : T){f : (T) => Unit}: Unit {
    f(v)
}

def indirectMyGreeter() {
    try {
        var capturedGreeter = greeter;
        val bar = {() => (unbox capturedGreeter).sayHello()};
        invoke(bar){(f : (() => Unit at {greeter})) => f()}
    } with greeter : Greeter {
        def sayHello() {
            println("Hello World!");
            resume(())
        }
    }
}
```