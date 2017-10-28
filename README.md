flutterbyeƸ̵̡Ӝ̵̨̄Ʒ
=============

introduction
------------

the goal of the *flutterbye* project is to produce tools that can be used to develop verifiable [concurrent programs](https://en.wikipedia.org/wiki/Concurrent_computing), with the long-term goal of producing an [actor](https://en.wikipedia.org/wiki/Actor_model) language and runtime used to safely describe concurrency.

nearly all computer programs are concurrent to some degree. unfortunately, software verification tools do not reason about the ordering of operations with ease and the lack of a strategy to address concurrency in computer programs remains a obstacle to the practical application of the verification. for this reason, verification of concurrency remains a tantalizing prize to the research community.

another important motivation for *flutterbye* is to bring awareness to the common practice of ignoring side-effects and implicit behavior in software development, which inevitably leads to systems that not only fail unpredictably but also prove to be difficult to diagnose and repair.

development status
------------------

this is an early work in progress of an experimental work. please expect things to be broken and unexpected changes in direction.

currently, effort is being focused on documentation and proofs.

getting started
---------------

### setup

creation of a development environment is fully automated using [vagrant](http://vagrantup.com) and [virtualbox](http://virtualbox.org). to get started:

1. download and install [vagrant](http://vagrantup.com).
2. download and install [virtualbox](http://virtualbox.org).
3. type `vagrant plugin install vagrant-vbguest` to install the [`vagrant-vbguest`](https://github.com/dotless-de/vagrant-vbguest) plugin (optional but recommended).
4. type `vagrant up` to prepare a new development environment.

### usage

#### startup
- `vagrant halt` will shut down the environment.
- `vagrant ssh` is used to access commands within the development environment.
- once in the container, type `cd /vagrant` to place yourself in the project's root directory.

#### shutdown
- `exit` leaves the development environment.
- `vagrant halt` will shut the environment down cleanly.

license
-------

this work is licensed under the *Apache License 2.0*. please see the [NOTICE](./NOTICE) and [LICENSE](./LICENSE) files for more details.
