---
layout: default
title: Section 1
parent: Paper Examples
nav_order: 1
---

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