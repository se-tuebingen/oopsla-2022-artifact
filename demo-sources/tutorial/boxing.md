---
layout: page
title: Boxing and Unboxing
permalink: /boxing/
parent: Tutorial
nav_order: 3
---
# Boxing and Unboxing

As we observed earlier, by default functions and capabilites are second class -- they cannot be returned nor stored in mutable cells and can only be passed as second-class parameters to other functions.  We can lift this
restriction by _boxing_ these functions and capabilities, reifying the set of captured capabilites from the binder to the type.

```effekt
interface Greeter { def sayHello(): Unit }

def myGreeter() {
  try {
    // boxing a capability and storing it in a mutable variable
    var capturedGreeter = box greeter;

    // unboxing requires `greeter` to be in scope
    def user() { (unbox capturedGreeter).sayHello() }

    // automatic boxing of `user`, stored in a value binder
    val firstClassUser: () => Unit at {greeter} = user;

    // automatic unboxing of firstClassUser
    firstClassUser()
  } with greeter : Greeter {
    def sayHello() { println("Hello World!"); resume(()) }
  }
}
```

Here, we box `greeter` to store it in the mutable cell `capturedGreeter`.
Note that System C supports automatic boxing and unboxing, and we could have omitted `box`.
We can also explicitly annotate the expected capability set as `box {greeter} greeter`.
In the function `user`, we unbox the captured first-class block and call `sayHello`.
The fact that we unbox it is reflected in the inferred capability set annotated on `user`.

Boxed values act as normal first-class values in System C until unboxed.
In particular, they can be passed as values to value-polymorphic functions.
```effekt
def invoke[T](v : T){f : (T) => Unit}: Unit { f(v) }

def indirectMyGreeter { greeter: Greeter }: Unit {
  val capturedGreeter = box greeter;
  invoke(capturedGreeter){ (f : Greeter at { greeter }) =>
    f.sayHello()
  }
}
```
Hovering over `capturedGreeter` shows how the capture is reflected in the type.

## Reasoning about Purity
Boxes reflect capture of tracked variables in their types. Let us assume the following function
in the standard library:
```effekt
// def setTimeout(callback: () => Unit at {}, duration: Int): Unit
```
Its implementation uses the FFI to JavaScript.
System C is implemented as a compiler to JavaScript and requires a monadic runtime. The value passed to
the JavaScript builtin `window.setTimeout` should not make use of any control effects or effect handlers
since it will be called later outside of all possible handlers.
To express this, we require the callback to be "pure" (i.e. `() => Unit at {}`).

We can still use the unsafe `println` function, as illustrated in the following example
```effekt:repl
setTimeout(box { () => println("Hello after 2 seconds!") }, 2000)
```