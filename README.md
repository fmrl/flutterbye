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

getting started
---------------

### setup

creation of a development environment is fully automated using [vagrant](http://vagrantup.com). to get started:

1. install [vagrant](http://vagrantup.com).
2. install [virtualbox](http://virtualbox.org).
3. make a copy of `Vagrantfile.sample` and call it `Vagrantfile`. you may modify this file if you wish.
4. type `vagrant up` to prepare a new development environment. `vagrant halt` will shut down the environment and `vagrant ssh` can be used to access commands within the development environment.  

#### alternatives

using virtualbox is convenient but, of course, performs poorly compared to containers or bare-metal installations of tools. 

linux users, in theory, have the option to substitute a container technology (e.g. `lxc` or `docker`) but i haven't yet explored these options fully. alternatively, linux users can configure their system without the use of vagrant: studying the scripts in `lib/vagrant` should provide sufficient documentation for this endeavor.

windows users, may have more difficulty configuring their system without using a virtual machine. i recommend building the ocaml version of [f*](http://fstar-lang.org) but ocaml support for windows is still very experimental (i.e. not for the faint of heart). if you're feeling brave, however, refer to the [f*](http://fstar-lang.org) for guidance.

license
-------

this work is licensed under the *Apache License 2.0*. please see the [NOTICE](./NOTICE) and [LICENSE](./LICENSE) files for more details.
