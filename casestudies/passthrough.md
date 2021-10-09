---
layout: default
title: Use and Mention
parent: Case Studies
nav_order: 2
---

## Distinguishing between Use and Mention

One issue with capability-based effect systems is that they often fail to distinguish between the actual
usage of a capability from when a capability is simply mentioned or passed through a section of code.
Consider the following example, where we are given two capabilities, one for reading from and one for
writing to a cell in memory:

```effekt
interface Write[T] {
  def write(value: T): Unit
  def read(): T
}
interface Read[T] { def read(): T }

// Section 2.1 shows with a simple example how mention is to coarse grained
// we can encode the effect-system variant that allows paralellization
def section2_1[T] { x : Read[T] } { y: Write[T] }  {

  val parallelizeMe: () => Unit at {} = box { () =>

    // here we mention `y`, but do not really "use" it.
    def z1(v: T) { y.write(v) }

    // same here.
    val z2 = box { () => y.write(<>) };

    ()
  };
  ()
}
```

In more traditional capability systems we would observe that `parallelizeMe` captures the write capability `y`
and hence could not be parallelized safely.  However, as the only mentions of `y` are behind a function `z1` which
is never called and an inert boxed value `z2` System C can safely conclude that `parallelizeMe` does not actually
use the `y` capability and can be safely parallelized.  This is indiciated by the type assigned to it, which is
`() => Unit at {}` -- a boxed thunk which requires no capability at usage (unboxing).

This is perhaps a bit of a contrived example, but System C also deals with similar problems that come up
in real life.  Consider an common example due to Gordon [2020]; we have a UI, for which computation which
modifies the UI must take place on dedicated UI threads.

```effekt
interface UI { def use(): Unit }

// Section 2.3 argues that capabilities are sometimes too coarse grained.
// The following example is difficult to express with capabilities and the authors also
// fell back to effect systems in their own related work.
def section2_3 { ui : UI } {

  def aliased = ui;

  def setLabel(text: String): Unit { ui.use() }

  def forkThread(run: () => Unit at {}): Unit { return () }
  def forkUIThread(run: () => Unit at {ui}): Unit { return () }

  forkThread({() =>
    val tmp = 42;

    forkUIThread({() =>
      setLabel("The result is " ++ show(tmp))
    })
  });
  ()
}
```

Here, (perhaps due to bad, pre-existing library design), we are given a global UI capability which must be
passed through a background worker thread before it is sent to a thread which executes on the UI thread.
The intermediate thread cannot use the UI capability.  In a traditional capability system one would
again observe that since the function passed to forkThread indirectly captures the UI capability, System C is
able to accurately observe that it never uses it and hence can be safely run.
