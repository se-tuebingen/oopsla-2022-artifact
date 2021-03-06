---
layout: default
title: Tutorial
has_children: true
nav_order: 1
---

# Tutorial of System C

In this interactive demo we will take you through a
brief introduction to System C and a quick tour of its features.

> _You can find all examples from the paper on [this page](../paper.html)._


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
