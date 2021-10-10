---
layout: default
title: Use and Mention
parent: Case Studies
nav_order: 2
---

## Distinguishing between Use and Mention

As observed by [Colin Gordon (2020)](https://drops.dagstuhl.de/opus/volltexte/2020/13167), one issue with capability-based effect systems is that they often fail to distinguish between the actual
usage of a capability from when a capability is simply mentioned or passed through a section of code.
Consider the following example, where we are given two capabilities, one for reading from and one for
writing to a cell in memory:

```effekt
interface Write[T] {
  def write(value: T): Unit
  def read(): T
}
interface Read[T] { def read(): T }

def fork(pureFunction: () => Unit at {}): Unit { () }

def mereMention[T] { x : Read[T] } { y: Write[T] }  {

  fork(box { () =>
    // here we mention `y`, but do not really "use" it.
    def z1(v: T) { y.write(v) }

    // same here.
    val z2 = box { () => y.read() };
    ()
  });
  ()
}
```

In more traditional capability systems we would observe that the boxed blocked passed to `fork` captures the write capability `y`
and hence could not be parallelized safely. However, as the only mentions of `y` are (1) behind a function `z1`, which
is never called and (2) an inert boxed value `z2`, System C can safely conclude that we do not actually
use the `y` capability and can safely call `fork`.  This is indiciated by the type assigned to it, which is
`() => Unit at {}` -- a boxed thunk which requires no capability at usage (unboxing).

This example might be perhaps a bit contrived, but System C also deals with similar problems that come up
in real life.  Consider an example due to Gordon; we have a UI, for which computation which
modifies the UI must take place on dedicated UI threads.

```effekt
interface UI { def use(): Unit }

interface Field { def setLabel(text: String): Unit }

def application { ui : UI } {

  def field = new Field {
    def setLabel(text: String) { ui.use() }
  };

  def forkThread(run: () => Unit at {}): Unit { return () }
  def forkUIThread(run: () => Unit at {ui}): Unit { return () }

  forkThread({() =>
    val tmp = 42; // some expensive computation

    forkUIThread({() =>
      field.setLabel("The result is " ++ show(tmp))
    })
  });
  ()
}
```

Here, we are given a global UI capability which must be
passed through a background worker thread before it is used to report the final result on the UI thread.
The intermediate thread must not use the UI capability.
A more traditional capability system would conservatively approximate that the function passed
to `forkThread` closes over `field`, which in turn closes over `ui`.
In contrast, System C is able to accurately observe that it never uses it and hence can be safely run.
