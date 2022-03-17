---
layout: default
title: Section 2
parent: Paper Examples
nav_order: 1
---

### Section 2 -- Introduction
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

### Section 2.2 -- Effect Safety
We can express the example of rethrowing exceptions in System C as follows:

```effekt
def rethrow
    {f: String => String}
    {p: {Exc} => Unit}
    {outerExc: Exc}: Unit {
      try { p {exc} }
      with exc: Exc {
        def throw(msg: String) { outerExc.throw(f(msg)) }
      }
}
```

```effekt
interface Info { def get(): String }
def prependInfo {prog: {Exc} => Unit} {info: Info} {exc: Exc}: Unit {
  rethrow { (msg: String) => info.get() ++ " " ++ msg } {prog} {exc}
}
```

```effekt
def runExample() {
  try {
    prependInfo { {exc: Exc} => exc.throw("Boom!") } {info} {exc}
  } with exc: Exc {
    def throw(msg: String) { println(msg) }
  } with info: Info {
    def get() { resume("[INFO]") }
  }
}
```


```effekt:repl
runExample()
```