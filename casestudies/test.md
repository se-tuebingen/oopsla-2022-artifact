---
layout: default
title: Test
parent: Case Studies
nav_order: 2
---

## Test Case Study

```effekt
interface Console { def log(msg: String): Unit }

def sayHello { c: Console }: Unit = {
  def foo() = c.log("sdfsdf")
  println("Hello World!")
}
```