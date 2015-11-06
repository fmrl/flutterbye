(*--build-config
   options:--admit_fsi FStar.Seq;
   other-files:seq.fsi Flutterbye.Seq.Insert.fsi
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

module Flutterbye.Specs.Remove
   open FStar.Seq

   val remove:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> 'a
      -> Tot (seq 'a)

   val lemma__length:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures (length (remove s i a) = length s - 1))
         [SMTPat (length (remove s i a))]

   val lemma__content:
      s: seq 'a{length s > 0}
      -> i: nat{i < length s}
      -> a: 'a
      -> Lemma
         (requires (True))
         (ensures
            ((forall j. 0 <= j && j < i
               ==> index (remove s i a) j = index s j)
            /\ (forall j. i <= j && j < length (remove s i a)
               ==> index (remove s i a) j = index s (j + 1))))
         // todo: need trigger
