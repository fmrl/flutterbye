(*--build-config
   options:--admit_fsi FStar.Seq --admit_fsi Flutterbye.Seq.Mem --admit_fsi Flutterbye.Seq.Filter;
   other-files:seq.fsi Flutterbye.Seq.Mem.fsi Flutterbye.Seq.Filter.fsi Flutterbye.Seq.Count.fsi
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

module Flutterbye.Seq.Count
open FStar.Seq
open Flutterbye.Seq.Filter

// todo: it's too easy to define something and accidentally mismatch what's in
// the `.fsi` file, causing f* to declare something as verifying were the user
// has actually unwittingly discared all verification conditions.
let count p s =
   Flutterbye.Seq.Filter.lemma__length p s;
   length (filter p s)
