---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: home
title: Home
nav_order: 0
---


# Effects, Capabilities, and Boxes

Welcome to our artifact website!

Our artifact consists of the following components:

- [**Coq Proofs**](proofs/). We documented our Coq proofs, highlighting the most important aspects and contrasting the definitions with the paper.
  We recommend you look at the [definitions](./proofs/Top.SystemC.Definitions.html) as well as at the [theorems](./proofs/Top.SystemC.Soundness.html).

- [**Interactive Demo**](intro.html). This website contains additional [casestudies](casestudies.html), [examples from the paper](paper.html),
  and additional explanation on [capabilities](capability) and [boxing](boxing). All examples can be typechecked and edited in the browser!


## Interactive Demo
In this interactive demo we will take you through a
brief introduction to System C and a quick tour of its features.

> _You can find all examples from the paper on [this page](paper.html)._


### Editors

In general, you will find a lot of small code snippets that can you can typecheck and run in the browser.
For example, this is a program that prints out "Hello World!". Try clicking _typecheck and run_ to load the editor (this can take a while the first time).
```effekt
def sayHello(): Unit {
  println("Hello World!")
}
```
The editor comes with basic support for System C -- try hovering over `println`!

You can also modify the program and then click _typecheck and run_ again to run the typechecker.
Alternatively, in the editor you can also use the keybinding `<CTRL+Enter>` on Windows or `<CMD+Enter>` on MacOS.

### REPLs
Sometimes you will also find REPL windows. To run the code example, just click the _run_ button!
```effekt:repl
sayHello()
```
Like with other editors, you can freely change the REPL input. Since REPLs are always single-line, you can simply press `<ENTER>` instead of clicking _run_.