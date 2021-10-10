---
layout: default
title: Case Studies
nav_order: 4
has_children: true
permalink: /casestudies
---

# Case Studies
Here we report on (additional) examples that illustrate the expressivity of System C.


## Examples from the Paper

### Section 1 -- Introduction
```effekt
interface Exc { def throw(msg: String): Unit }
type File { FileHandle(id: Int) }

def eachLine(file: File) { f: String => Unit }: Unit { () }
def open(path: String) {exc:Exc}: File { FileHandle(0) }

def process(path: String) {exc1: Exc}: Unit {
  def abort(): Unit { exc1.throw("processing aborted") }
  try { eachLine(open(path){exc2}) { (line: String) => abort() } }
  with exc2: Exc { def throw(msg: String) { () }}
}
```

### Section 2 -- Global Capabilities
```effekt
interface Console { def println[A](a: A): Unit }
interface Time { def now(): Int }

// console and time are "global" -- that is, module wide capabilities
def globalCapabilities { console: Console } { time: Time }: Unit {

  def sayTime() {
    console.println("The current time is: " ++ show(time.now()))
  }

  // other blocks closing only over console or time
  def sayHello() { console.println("Hello!") }
  def currentTime() { time.now() }

  def repeat(n: Int) { f: () => Unit }: Unit {
    if (n == 0) { () } else { f(); repeat(n - 1) {f} }
  }

  repeat(3) { () => console.println("Hello!") };
  repeat(3) { () => sayTime() };

  def parallelWrong { f: () => Unit } { g: () => Unit }: Unit { () }

  // this wrong definition admits the following call:
  parallelWrong
    { () => console.println("Hello, ") }
    { () => console.println("world!") };

  // "correct" specification
  def parallel(f: () => Unit at {}, g: () => Unit at {}): Unit { () }

  // try commenting out the below call to see type errors
  // parallel(
  //   box { () => console.println("Hello, ") },
  //   box { () => console.println("world!") });

  // same here, this is illtyped:
  // val firstClassWrong = box {} { () => console.println("Hello, ") };

  val firstClassInfer = box { () => sayTime() };

  def sayTimeThrice(): Unit { repeat(3) { () => sayTime() } }


  // 2.1.4 Capability Polymorphism
  def repeater { f: () => Unit }: (Int) => Unit at { f }
  { return box { (n: Int) => repeat(n) {f} } }

  val repeatTime = repeater { sayTime };

  // some more variants illustrating closure and capability sets
  val b = sayTime;

  val n = repeater { () => sayTime() };
  val n1 = repeater { sayTime };
  val b2 : () => Unit at {console, time} = box { () => (unbox n)(3) };
  val b3 = n(3);
  val b4 = { () => n(3) };
  val r = repeater { b };

  ()
}
```

### Section 2 -- Local Capabilities and Effect Handlers
```effekt
interface Stopwatch { def elapsed(): Int }
def localCapabilities { console: Console } { time: Time }: Unit {
  try { console.println("hello"); exc.throw("world"); console.println("done") }
  with exc: Exc {
    def throw(msg: String) { console.println(msg ++ "!") }
  };

  // uncomment the following example to see a type error:
  // try { return (box exc) } with exc: Exc { def throw(msg: String) { () } };

  val before = time.now();
  try {
    console.println(watch.elapsed())
  } with watch: Stopwatch {
    def elapsed() {
      // we can observe the capture of `resume` by boxing it:
      val k = box resume;
      resume(time.now() - before)
    }
  };

  ()
}
```

### Support Code for Running
```effekt
def runExamples(): Unit {
  try {
    globalCapabilities {console} {time};
    localCapabilities {console} {time}
  } with console: Console {
    def println[A](msg: A) { println(msg); resume(()) }
  } with time: Time {
    def now() { resume(timestamp()) }
  }
}
```
```effekt:repl
runExamples()
```