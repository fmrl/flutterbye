flutterbyeƸ̵̡Ӝ̵̨̄Ʒ
=============

goals and motiviation
---------------------

the goal of the *flutterbye* project is to produce tools that can be used to develop verifiable [concurrent programs][concurrent computing on wikipedia], with the tentative long-term goal of producing an [actor][actor model on wikipedia] language and runtime used to safely describe concurrency.

nearly all computer programs are concurrent to some degree. unfortunately, software verification tools do not reason about the ordering of operations with ease and the lack of a strategy to address concurrency in computer programs remains a obstacle to the practical application of the verification. for this reason, verification of concurrency remains a tantalizing prize to the research community.

another important motivation for *flutterbye* is to bring awareness to the common practice of ignoring side-effects and implicit behavior in software development, which inevitably leads to systems that not only fail unpredictably but also prove to be difficult to diagnose and repair.

introduction
------------

### software verification

verified languages such as [dafny] attempt to reconcile the implementation of a program against a mathematical proof of its behavior through a concept called refinement. this is similar to the relationship between base classes and derived classes in object oriented methodology, where a base class provides an abstract representation of a type and a derived type implements concrete behavior.

in an object-oriented language, one could imagine a base class that also defines semantics for a particular method (e.g. invoking `int Next(int x)` must result in a value that is one greater than `x`, but not exceed the maximum value of an `int`). simple interface definitions in popular languages cannot place (nor enforce) expectations on their implementations beyond what the type system permits and we must assume that any given implementation works as the interface documentation suggests.

*refinment relationships* strengthen the *generalization relationship* between an abstract definition of program behavior (referred to as a *specification* or *proof*) and its concrete implementation. [dafny], for example, uses a constraint language based on [contract programming][design by contract on wikipedia] in definitions of abstract modules to declare and enforce semantics upon implementation modules declared to be refinements of the abstract module definition. continuing with the previous object-oriented example, a derived class that refines its base class would be required to implement some sort of method that satisfies the semantics defined by the constraint language.

the implications of this are important. one could begin with a simple implementation of a method that is not performant but satisfies the requirements of the specification and later provide an performant implementation that satisfies the requirements of the same specification. assuming the specification is sufficiently strong, a programmer can have an assurance that the new implementation behaves identically to the old code.

languages that support software verification such as [dafny], [f\*], and [ivy], can be thought of as relying upon a sophisticated software stack that either enhances or replaces what we would normally categorize as a compiler's type system or static analysis (e.g. [coverity]). the base of this software stack for static analysis is some sort of constraint solver or theorem prover, such as [z3].

### current limitations of software verification

one unfamiliar with the internals of this new software stack can imagine it as a black box containing a special-purpose intelligence that reasons, through deduction, about a program's behavior and what things we can be certain about, given a set of statements that we assume to be true. while being the same kind of activity skilled programmers engage in, it is a common mistake to setting expectations that software verification reasons about everything as well as we could or in a manner that we find intuitive. given a correct and adequate set of inputs, a software verification stack can reason more precicely about a subset program's behavior than a human. it, however, does not reason well under the following conditions:

- an excess of facts about the program.
- contradictory facts about the program.
- unpredictable ordering of operations in the program.

the first two issues affect scalability of software verification and reasonable solutions seem to exist to address these issues. the third issue, however, remains problematic because it is arguably impossible to reason about all possible orderings of actions taken by an arbitrary program (i.e. *side-effects*). this also is at the heart of the problem that concurrency presents in software and includes phenomena that we consider staples of familiar programming languages:

- shared state (e.g. heap interactions & aliasing).
- mutable state.
- parallelism.
- co-routines.

these concepts seem unquestioningly intuitive to us and we actively construct enormously complicated systems, despite their troublingly implicit presence in how modern programs are expressed. even the most skilled reasoning about these mechanisms is error prone, however, as evidenced by the number of times concurrent systems tend to fail unexpectedly due to bugs in the code and the inability to predict when those failures will occur.

### thinking locally

development status
------------------

this is an early work in progress of an experimental work. please expect things to be broken and unexpected changes in direction.

currently, effort is being focused on documentation and proofs.

getting started
---------------

### setup

creation of a development environment is fully automated using [vagrant] and [virtualbox]. to get started:

1. download and install [vagrant].
2. download and install [virtualbox].
3. type `vagrant plugin install vagrant-vbguest` to install the [`vagrant-vbguest`][vagrant-vbguest] plugin (optional but recommended).
4. type `vagrant up` to prepare a new development environment.

#### alternatives to virtualbox

using *virtualbox* is convenient but, of course, performs poorly compared to containers or bare-metal installation of tools.

linux users may prefer to use the [vagrant `docker` provider] instead, provided that [docker] is installed and functioning. alternatively, linux users can configure their system without the use of vagrant: studying the scripts in `scripts/setup` should provide sufficient documentation for this endeavor, starting with `scripts/setup/vagrant.sh`.

windows users, will have more difficulty configuring their system without using a virtual machine. the [vagrant `docker` provider] is working, in theory, but i have found vagrant's hyper-v integration to be a work-in-progress. if neither hyper-v nor virtualbox are viable options, i recommend folowing the spirit of the setup scripts with windows equivalents. building the ocaml version of [f\*] is not for the faint of heart, however, because ocaml support for windows is still very experimental. if you're feeling brave refer to the [f\*] for guidance.

### usage

#### startup
- `vagrant halt` will shut down the environment.
- `vagrant ssh` is used to access commands within the development environment.
- once in the container, type `cd /vagrant` to place yourself in the project's root directory.

#### build tool (rake)
- type `rake` to build the project. currently, this just verifies what proofs have been written.
- if you don't care to verify all modules, you can instead type `rake fstar:verify[MODULES]` where *MODULES* is a globbing pattern that will be used to constrain which modules are verified (e.g. `rake fstar:verify [*.Linear*]`).
- you may also specify a timeout in seconds (e.g. `rake fstar:verify [*.Mem,10]`).

#### shutdown
- `exit` leaves the development environment.
- `vagrant halt` will shut the environment down cleanly.


license
-------

this work is licensed under the *Apache License 2.0*. please see the [NOTICE] and [LICENSE] files for more details.

-----

[actor model on wikipedia]: https://en.wikipedia.org/wiki/Actor_model
[concurrent computing on wikipedia]: https://en.wikipedia.org/wiki/Concurrent_computing
[dafny]: https://github.com/Microsoft/dafny
[docker]: https://www.docker.com/
[f\*]: http://fstar-lang.org
[LICENSE]: ./LICENSE
[NOTICE]: ./NOTICE
[vagrant `docker` provider]: https://www.vagrantup.com/docs/docker/
[vagrant `hyperv` provider]: https://www.vagrantup.com/docs/hyperv/
[vagrant-vbguest]: https://github.com/dotless-de/vagrant-vbguest
[vagrant]: http://vagrantup.com
[virtualbox]: http://virtualbox.org
[design by contract on wikipedia]: https://en.wikipedia.org/wiki/Design_by_contract
[ivy]: https://github.com/Microsoft/ivy
[z3]: https://github.com/Z3Prover/z3
[coverity]: https://www.coverity.com/
