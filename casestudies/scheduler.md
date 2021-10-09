---
layout: default
title: Scheduling (with continuations and mutable cells)
parent: Case Studies
nav_order: 2
---

Writing a safe, co-operatively threaded scheduler can be hard, as continuations can leak, and one does not want handles to the
scheduler (with the capability to fork new threads and yield within the scheduler) to leak outside of the scheduler itself.
System C can safely express this though.

```effekt
interface Scheduler {
    def yield(): Unit
    def fork(): Boolean
}

def schedule {program : {Schedule} => Unit} {
    region scheduler {
        var state in scheduler = box {scheduler, sched} {() => ()} ;
        try {
            ()
        } with sched : Scheduler {
            def yield() {
                state = {() => resume(())};
                ()
            }
            def fork() {
                resume(true);
                resume(false)
            }
        }
    }
}

def main() {
    ()
}
```