// $legal:629:
//
// Copyright 2016 Michael Lowell Roberts & Microsoft Research
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
//,$

module Flutterbye.Seq

type disjoint_p = Flutterbye.Seq.Disjoint.disjoint_p
type mem_p = Flutterbye.Seq.Mem.mem_p
type unique_p = Flutterbye.Seq.Unique.unique_p

let count = Flutterbye.Seq.Count.count
let dedup = Flutterbye.Seq.Unique.dedup
let disjoint = Flutterbye.Seq.Disjoint.disjoint
let filter = Flutterbye.Seq.Filter.filter
let find = Flutterbye.Seq.Find.find
let insert = Flutterbye.Seq.Insert.insert
let map = Flutterbye.Seq.Map.map
let mem = Flutterbye.Seq.Mem.mem
let remove = Flutterbye.Seq.Remove.remove
let satisfies = Flutterbye.Seq.Satisfies.satisfies

let to_set = Flutterbye.Seq.ToSet.to_set
let unique = Flutterbye.Seq.Unique.unique
