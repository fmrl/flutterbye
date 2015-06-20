notes on tesseract
==================

*please consider this document an early work in progress.*

## hewett actors

- carl hewett
- hewett actors oversimplified:
    - structure-sized, usu. single-threaded process
    - communication via async messsage passing
    - permits distributed programming reasoning in more contexts.
- modern examples:
    - mantrid
    - erlang
    - orleans
    - akka   

## effectful actors

## total actors

- defined as the tuple `(S0 * M * F)` where:
    - `S0` is the actor's initial state.
    - `M` is a sequence of messages processed by the actor.
    - `F` is a total function that transforms a message and a state into a new state and a sequence of messages.
- don't send messages; rather, they specify messages to be sent by an unspecified runtime.

## modeling effects

- *effect systems* are formal systems used to model effects.
    - separate (side-)effects from pure values.  
- a **total actor system** separates pure values from (side-)effects also.
- so, given a total actor system whose messages are used to represent (only) effects, we have an effect/actor system i will call an *effectful actor system*.
- we will use the language of effects in place of actor vernacular at times.

## effect regions
- an actor in an effectful actor system is called an *effect region*.
- an region shall be described with the total actor tuple `(S0 * E * C)` where:
    - `S0` is the region's initial state.
    - `E` is a sequence of effects applied to the actor state.
    - `C` is the **causal transform**, a function that expresses a an atomic causal operation on a given effect region.

## primitive effect kinds
- **spawn**: initialize a region, readying it to be affected.
- **step**: influence a region, advancing causality in an atomic fashion.

            
-----
Copyright 2015 Michael Lowell Roberts

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

