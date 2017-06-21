flutterbyeƸ̵̡Ӝ̵̨̄Ʒ
=============

goals and motiviation
---------------------

the goal of the *flutterbye* project is to produce tools that can be used to develop verifiable [concurrent programs][concurrent computing on wikipedia], with the tentative long-term goal of producing an [actor][actor model on wikipedia] language and runtime used to safely describe concurrency.

nearly all computer programs are concurrent to some degree. unfortunately, software verification tools do not reason about the ordering of operations with ease and the lack of a strategy to address concurrency in computer programs remains a obstacle to the practical application of the verification. for this reason, verification of concurrency remains a tantalizing prize to the research community.

another important motivation for *flutterbye* is to bring awareness to the common practice of ignoring side-effects and implicit behavior in software development, which inevitably leads to systems that not only fail unpredictably but also prove to be difficult to diagnose and repair.

introduction
------------

*this section is a work in progress; please consider it incomplete and inaccurate while it is being written and edited.*

### software verification

languages that support software verification can be thought of as using a sophisticated software stack for code analysis that reasons about code without having to execute it, as type systems and static analysis tools such as [coverity] are known to do. a software verification stack may [compliment a conventional type system][dafny], [extend a conventional type system][f\*], or even [displace conventional type systems][ivy]. usually, the base layer of this software stack for static analysis is some sort of constraint solver or theorem prover, such as [z3].

[dafny], for example, attempts to reconcile the implementation of a program against a mathematical proof of its behavior through a concept called refinement. this is similar to the relationship between base classes and derived classes in object oriented methodology, where a base class provides an abstract representation of a type and a derived type implements concrete behavior.

in an object-oriented language, one could imagine a base class that also defines semantics for a particular method (e.g. invoking `int Next(int x)` must result in a value that is one greater than `x`, but leave the value unchanged if the result would exceed the maximum permitted value of an `int`). simple interface definitions in popular languages cannot place (nor enforce) expectations on their implementations beyond what the type system permits and we must assume that any given implementation works as the interface documentation suggests.

*refinment relationships* strengthen the more conventionally understood *generalization relationship* between an abstract definition of program behavior (referred to as a *specification* or *proof*) and its concrete implementation by including a description of semantics in the abstraction. [dafny], for example, uses a constraint language based on [contract programming][design by contract on wikipedia] in definitions of abstract modules to declare and enforce semantics upon implementation modules declared to be refinements of the abstract module definition. continuing with the previous object-oriented example, a derived class that refines its base class would be required to implement some sort of method that satisfies the semantics expressed within the constraint language. despite the simplicity of the operation described by `Next`, one can imagine a more than one concrete implementation, each preferable over the others within a particular context.

the implications of this are important. one could begin with a simple implementation of a method that is not performant but satisfies the requirements of the specification and later provide an performant implementation that satisfies the requirements of the same specification. assuming the specification is sufficiently strong, a programmer can have an assurance that the new implementation behaves identically to the old code. software verification promises an increase in accountability for people who produce software: a manager, through this mechanism, can meaningfully elicit quality code from her team because there is a measurable standard of quality available before deployment; likewise, a programmer can credibly counter agressive and unrealistic requests to deliver results from management on the basis that the formal specification is not yet provably satisfied.

### current limitations of software verification

one unfamiliar with the internals of this alternative software stack for static analysis can imagine it as a black box containing a [special-purpose, reactive intelligence][myth of a superhuman ai] that reasons, through a portfolio of strategies that ultimately amount to a deduction process, about a program's behavior and what things we can be certain about, given a set of statements that we assume to be true and a set of statements that we hope to be true. while this reasoning process is similar to the kind of activity skilled programmers engage in, a software verification stack can reason more reliably about a program's behavior than a human could. it is a common mistake, however, to set expectations that the theorem prover reasons about everything as well as we could or in a manner that we find intuitive; for example, a theorem prover does not reason well about:

- contradictory facts about the program.
- an excess of unnecessary facts about the program.
- unpredictable ordering of operations in the program.

the first two issues affect the scalability of software verification and reasonable solutions more-or-less exist to address these issues given sufficient effort (e.g. proper analysis feedback and module opacity). the third issue, however, remains problematic because it is arguably impossible to reason about all possible orderings of actions taken by an arbitrary program (i.e. reason about *side-effects*). this also is at the heart of the problem that concurrency presents to humans in software, even though we consider ourselves qualified, often uncritically, to reason about:

- shared state (e.g. heap interactions & aliasing).
- mutable state.
- parallelism.
- co-routines.

herein lies to origins of the infamous, unpredictable concurrency bugs that computer scientists have yet to really find consensus regarding how to tame.

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
[coverity]: https://www.coverity.com/
[dafny]: https://github.com/Microsoft/dafny
[design by contract on wikipedia]: https://en.wikipedia.org/wiki/Design_by_contract
[docker]: https://www.docker.com/
[f\*]: http://fstar-lang.org
[ivy]: https://github.com/Microsoft/ivy
[LICENSE]: ./LICENSE
[NOTICE]: ./NOTICE
[vagrant `docker` provider]: https://www.vagrantup.com/docs/docker/
[vagrant `hyperv` provider]: https://www.vagrantup.com/docs/hyperv/
[vagrant-vbguest]: https://github.com/dotless-de/vagrant-vbguest
[vagrant]: http://vagrantup.com
[virtualbox]: http://virtualbox.org
[z3]: https://github.com/Z3Prover/z3
[myth of a superhuman ai]: https://backchannel.com/the-myth-of-a-superhuman-ai-59282b686c62
