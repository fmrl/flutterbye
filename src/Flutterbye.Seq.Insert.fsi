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

module Flutterbye.Seq.Insert
   open FStar.Seq

   val insert:
      s: seq 'a
      -> i: nat{i <= length s}
      -> 'a
      -> Tot (seq 'a)

   val lemma__length:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (length (insert s i a) = length s + 1))
         [SMTPat (length (insert s i a))]

   val lemma__content:
      s: seq 'a
      -> i: nat{i <= length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            (index (insert s i a) i = a
            /\ (forall j. 0 <= j && j < i
               ==> index (insert s i a) j = index s j)
            /\ (forall j. i < j && j < length (insert s i a)
               ==> index (insert s i a) j = index s (j - 1))))
         // todo: need trigger.