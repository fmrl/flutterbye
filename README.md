flutterbyeƸ̵̡Ӝ̵̨̄Ʒ 
=============

introduction
------------

**flutterbye** is an experimental [operational semantics](https://en.wikipedia.org/wiki/Operational_semantics) that uses a variation of the [actor model](https://en.wikipedia.org/wiki/Actor_model) to explicitly model [concurrency in computer programs](https://en.wikipedia.org/wiki/Concurrent_computing).

concurrent (and by extension, distributed) computer programs expressed in *flutterbye*'s semantics are predicted to have the following advantages:

- no implicit program behavior (i.e. no [action at a distance](https://en.wikipedia.org/wiki/Action_at_a_distance_%28computer_programming%29)).
- automatically scalable, both horizontally and vertically, through static analysis.
- usable in mathematical proofs of the soundness of the system.
- familiar to distributed systems programmers and programmers familiar with the actor system.
- permit "replay" and "rewind" of relevant concurrent logic in a debugger.
- permit automated logging of crucial events needed to support replay and rewind in a debugger.
- eliminates the need for ad-hoc logging of state transitions in code normally needed to make debugging concurrent systems effective.

most computer programs are concurrent in nature. an important motivation in *flutterbye*'s development is to bring awareness to how the common practice of ignoring side-effects and implicit behavior in software development leads to systems that fail unpredictably and prove difficult to diagnose and repair.

development status
------------------

this is an early work in progress of an experimental work. currently, effort is being focused on documentation and mathematical proofs describing *flutterbye*. long term goals will include working systems that demonstrate *flutterbye*.

license
-------

this work is licensed under the *Apache License 2.0*. please see the [NOTICE](./NOTICE) and [LICENSE](./LICENSE) files for more details.
