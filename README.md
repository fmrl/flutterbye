flutterbye🦋
============

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

#### method of interaction

the information consumed by the theorem prover is expressed in some sort or constraint language (usually predicate-based). this specification usually consists of:

- statements that the constraint solver may take for granted (*axioms* about *assumed invariants*).
- expectations that the constraint solver is expected to confirm or deny (*assertions* about *invariants*, or *verification conditions*)
- connective statements that inform the constraint solver about how to deductively arrive at a decision about given assertions from provided assumtions.

each stated invariant represents a [decision problem] that the constraint solver must solve, meaning that the constraint solver may answer each assertion with one of the three following answers:

- *yes*, meaning that there is sufficient information to deduce that a given assertion is true.
- *no*, meaning that there is sufficient information to deduce that a given assertion is false.
- *uncertain* (or *timeout*), meaning that there was either insufficient information to reason about the veracity of a given assertion within a specified time budget. the possibility that no amount of time would be sufficient exists if the decision problem presented to the theorem prover is [undecidable].

programmers spend a considerable amount of time and effort, when working with languages such as [dafny] and [f\*], to convert results that are *uncertain* into results that are *yes* or *no*. we suppose that this is because these languages consider preserving expectations connected to a particular programming language (e.g. [C#] or [Ocaml]) to be the priority and that these languages require the constraint solver to reason about undeciable problems, as best as it is able to, in order to preserve as much as possible of the status quo of programming language expectations. [ivy] takes a different approach: it is designed to guarantee decision certainty in exchange for the programmer sacrificing specific expectations of a programming language.

#### refinement

[dafny] attempts to reconcile the implementation of a program against a mathematical proof of its behavior through a concept called *refinement*. this is similar to the relationship between base classes and derived classes in object oriented methodology, where a base class provides an abstract representation of a type and a derived type implements concrete behavior.

in an object-oriented language, one could imagine a base class that also defines semantics for a particular method (e.g. invoking `int Next(int x)` must result in a value that is one greater than `x`, but leave the value unchanged if the result would exceed the maximum permitted value of an `int`). simple interface definitions in popular languages cannot place (nor enforce) expectations on their implementations beyond what the type system permits and we must assume that any given implementation works as the interface documentation suggests.

*refinment relationships* strengthen the more conventionally understood *generalization relationship* between an abstract definition of program behavior (referred to as a *specification* or *proof*) and its concrete implementation by including a description of semantics in the abstraction. [dafny], for example, uses a constraint language based on [contract programming][design by contract on wikipedia] in definitions of abstract modules to declare and enforce semantics upon implementation modules declared to be refinements of the abstract module definition. continuing with the previous object-oriented example, a derived class that refines its base class would be required to implement some sort of method that satisfies the semantics expressed within the constraint language. despite the simplicity of the operation described by `Next`, one can imagine a more than one concrete implementation, each preferable over the others within a particular context.

#### raison d'être

the implications of availability of this kind of automated reasoning are significant. one could begin with a simple implementation of a method that is not performant but satisfies the requirements of the specification and later provide an performant implementation that satisfies the requirements of the same specification. assuming the specification is sufficiently strong, a programmer can have an assurance that the new implementation behaves identically to the old code. software verification promises an increase in accountability for people who produce software: a manager, through this mechanism, can meaningfully elicit quality code from her team because there is a measurable standard of quality available before deployment; likewise, a programmer can credibly counter agressive and unrealistic requests to deliver results from management on the basis that the formal specification is not yet provably satisfied.

#### current limitations

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

### side-effects and concurrency

given that verification is known to have difficulty reasoning about the order of necessarily successive operations and that side-effects are the cause of such conditions, it is necessary to examine the gap that we wish to bridge.

in mathematics, a function is understood to be a relationship between one set of values and another. for example, in the following function definition, we describe integers and their successors:

```
function increment(x:bigint) returns y:bigint
{
   y = x + 1;
   return y;
}
```

assuming that the type `bigint` can describe any integer value, this is categorized as a *total function* because there is always an output value `y` for a given input value `x`. this kind of function is the simplest kind of function for the theorem prover to reason about because it describes a direct, predictable relationship between the function's arguments and it's computed result.

often, however, in programming we see functions such as the following:

```
function roll_die(sides:bigint) returns n:bigint
{
   bigint entropy = get_entropy();
   n = (entropy mod sides) + 1;
}
```

this function is *not* total and does not exhaustively describe an relation between the function's arguments and its computed result. additionally, the evaluation environment must perform actions in a specific order: first retrieve a random number, then transform the result that fits within the range of a die with the given number of sides.

the second of these actions can be described with a total function:

```
function roll_die(sides:bigint, entropy:bigint) returns n:bigint
{
   n = (m mod sides) + 1;
}
```

the first of these operation, however, is known as a *side-effect* and this kind of function is sometimes known as a *procedure* because of the side-effect's presence. the property of being a procedure is understandably transitive.

often, people from the functional programming community will make a claim that functional programs are free of side-effects. this is misleading at best. computer programs do nothing without side-effects-- the illusion of a die rolling does not function without a model of entropy. instead, when we separate side-effects from total functions, we say that the computation is *isolated* from any side-effects, but side-effects do not magically cease to exist because we find it inconvenient to find the words for them.

the functional programming community, however unaware of themselves they seem to be with statements declaring the non-existence of side-effects, have undergone a deeply beautiful effort to work out how to explicitly reason about side-effects and isolate them from computation. consider an idealized version of [erlang]: islands of state with event handlers, represented by total functions transforming an incoming message and the island's state into a list of outgoing messages and a state to succeed the input state. in this idealized model of erlang, the primitive used to express side-effects is the message. surely, erlang's proposition is that *side-effects are a model of communication with stateful entities* and that *this communication is the connective tissue between computations, represented by total functions*. [haskell], a more influential programming language, is better at isolating and specifying side-effects than the reality of erlang's programming model, but the primitive haskell uses for side-effects, the monad, is famous for being an elusive concept to grasp.

furthermore, unlike haskell, erlang's model plainly communicates why it is useful for side-effects to be isolated from computation. the islands of state and computation are  ordered and deterministic. they float in a sea of chaos-- a series of events whose order is not fully determined. in fact, absent specific knowledge about the protocol, we cannot determine the ordering of these side-effects, nor the order in which any total functions would be evaluated. we have, therefore, uncovered a compelling model that shows that communicaton between stateful entities, when it is yet-to-be-observed, necessarily flows within a medium of what we have come to know as concurrency.

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
[c#]: https://en.wikipedia.org/wiki/C_Sharp_(programming_language)
[concurrent computing on wikipedia]: https://en.wikipedia.org/wiki/Concurrent_computing
[coverity]: https://www.coverity.com/
[dafny]: https://github.com/Microsoft/dafny
[decision problem]: https://en.wikipedia.org/wiki/Decision_problem
[design by contract on wikipedia]: https://en.wikipedia.org/wiki/Design_by_contract
[docker]: https://www.docker.com/
[erlang]: https://www.erlang.org/
[f\*]: http://fstar-lang.org
[haskell]: https://www.haskell.org/
[ivy]: https://github.com/Microsoft/ivy
[LICENSE]: ./LICENSE
[myth of a superhuman ai]: https://backchannel.com/the-myth-of-a-superhuman-ai-59282b686c62
[NOTICE]: ./NOTICE
[ocaml]: https://en.wikipedia.org/wiki/OCaml
[undecidable]: https://en.wikipedia.org/wiki/Undecidable_problem
[vagrant `docker` provider]: https://www.vagrantup.com/docs/docker/
[vagrant `hyperv` provider]: https://www.vagrantup.com/docs/hyperv/
[vagrant-vbguest]: https://github.com/dotless-de/vagrant-vbguest
[vagrant]: http://vagrantup.com
[virtualbox]: http://virtualbox.org
[z3]: https://github.com/Z3Prover/z3
