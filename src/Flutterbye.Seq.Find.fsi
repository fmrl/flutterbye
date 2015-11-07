(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi
--*)

// $legal:614:
//
// Copyright 2015 Michael Lowell Roberts
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// ,$

module Flutterbye.Seq.Find
   open FStar.Seq

   // todo: this isn't working when used from a separate module.
   val option_get: o: option 'a{is_Some o} -> Tot 'a

   // todo: this should accept an 'a -> bool rather than an 'a.
   val find: s:'a -> seq 'a -> Tot (option nat)

   // todo: can this be broken down into simpler lemmas
   // (e.g. lemma__range and lemma__not_found)?
   val lemma__basic:
      a: 'a
      -> s: seq 'a
      -> Lemma
         (requires (True))
         (ensures
            ((is_None (find a s) ==>
               (forall j.
                  0 <= j && j < length s ==> index s j <> a))
            /\ (is_Some (find a s) ==>
                  ((option_get (find a s)) < length s
                  && a = index s (option_get (find a s))))))
         [SMTPat (find a s)]
