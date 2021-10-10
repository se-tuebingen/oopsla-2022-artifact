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

#### Support Code for Running Examples
```effekt
def run[T] { prog : {Console} {Time} => T }: T {
  try {
    prog {console} {time}
  } with console: Console {
    def println[A](msg: A) { println(msg); resume(()) }
  } with time: Time {
    def now() { resume(timestamp()) }
  }
}
```
We can run the above examples
```effekt:repl
run {globalCapabilities}
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
  ()
}
```
Again, we can run the above examples:
```effekt:repl
run {localCapabilities}
```

#### Example 2.1
```effekt
interface FileHandle { def readByte(pos: Int): Int }
def withFile[T](path: String) { prog: {FileHandle} => T }: T {
  try { prog {fh} } with fh: FileHandle {
    def readByte(pos: Int) { resume(pos + 42) }
  }
}
def fileExample() {
  withFile("A.txt") { {fileA: FileHandle} =>
    val offsetReader : Int => Int at {fileA} =
      withFile("B.txt") { {fileB: FileHandle} =>
        val offset = fileB.readByte(0);
        return box { (pos: Int) => fileA.readByte(pos + offset) }
      };
      (unbox offsetReader)(10)
  }
}
```
Running the example will print 92 (0 + 42 + 42 + 10).
```effekt:repl
fileExample()
```

#### Effect Handlers
```effekt
def effectHandlers { console: Console } { time: Time }: Unit {
  val before = time.now();
  try {
    def report(t: Int) { console.println(show(t) ++ "ms") }
    report(watch.elapsed());
    report(watch.elapsed());
    report(watch.elapsed())
  } with watch: Stopwatch {
    def elapsed() {
      // we can observe the capture of `resume` by boxing it:
      val k = box resume;
      resume(time.now() - before)
    }
  }
}
```
```effekt:repl
run {effectHandlers}
```

### Section 4.2 -- Mutable State
```effekt
interface State[S] {
  def get(): S
  def set(v: S): Unit
}
def handleState[S, R](init: S) { prog: {State[S]} => R }: R {
  val stateFun: S => R at {prog} =
    try { val res = prog { state }; return box {prog} { (s: S) => res } }
    with state: State[S] {
      def get() { box { (s: S) => (unbox resume(s))(s) } }
      def set(v: S) { box { (_: S) => (unbox resume(()))(v) } }
    };
  return (unbox stateFun)(init)
}
```
```effekt:repl
handleState(0) { {s: State[Int]} => println(s.get()); s.set(2); println(s.get()) }
```

For more details on regions, also see the corresponding [regions case study](regions).
```effekt
def regions1() {
  region r {
    var x in r = 42;
    val t = x;
    x = (t + 1)
  }
}
```
```effekt
def regions2() {
  region r {
    var x in r = 42;
    val f: () => Int at {r} = box { () => x };
    (unbox f)()
  }
}
```
```effekt:repl
regions2()
```