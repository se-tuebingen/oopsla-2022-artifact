---
layout: default
title: Case Studies
nav_order: 4
has_children: true
permalink: /casestudies
---

# Case Studies

Reasoning about the use of external resources is an important aspect of many practical applications.
Examples range from memory management, controlling access to privileged
resources like file handles or network,
to analysing the potential presence or absence of side effects.



```effekt
interface Console {
  def println[A](a: A): Unit

}
interface Time {
  def now(): Int
}

def testModule { console: Console } { time: Time } {

  def foo() {
    console.println("test");
    ()
  }

  def sayHello() { console.println("Hello!") }
  def currentTime() { time.now() }
  def sayTime() { console.println("The current time is: " ++ show(time.now())) }

  def repeat(n: Int) { f: () => Unit }: Unit { f() }

  def repeater { f: () => Unit }: (Int) => Unit at { f } {
    box { (n: Int) => repeat(n) {f} }
  }

  val b = sayTime;

  val n = repeater { () => sayTime() };
  val n1 = repeater { sayTime };
  val b2 : () => Unit at {console, time} = box { () => (unbox n)(3) };
  val b3 = n(3);
  val b4 = { () => n(3) };

  def even() { console.println("hello"); odd() }
  def odd(): Unit { even() }

  val r = repeater { b };

  def race(fst: () => Unit at {}, snd: () => Unit at {}): Unit { () }

  // race(
  //     box { () => console.println("hello") },
  //     box { () => console.println("world") });

  ()
}

def main() { () }
```
