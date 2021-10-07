---
layout: page
title: Boxing and Unboxing
permalink: /boxing/
nav_order: 3
---

As we observed earlier, by default functions and capabilites are second class -- they cannot be returned nor
stored in mutable cells and can only be passed as parameters to other functions.  We can lift this
restriction by _boxing_ these functions and capabilities, reifying the set of captured capabilites
from the binder to the type.

