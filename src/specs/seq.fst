(*--build-config
   other-files:ext.fst src/specs/set.fst src/specs/map.fst
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

module Tesseract.Specs.Seq
   open FunctionalExtensionality

   type _State 'item =
      | MkSeq:
         length: nat -> mapping: Map.map_g nat 'item -> _State 'item

   type SeqSafety: #item: Type -> seq: _State item -> Type =
      fun 'item (seq: _State 'item) ->
         ((0 = MkSeq.length seq) /\ (FEq (MkSeq.mapping seq) (fun _ -> None)))
         \/ (forall (index: nat).
               ((index < (MkSeq.length seq))
                  <==> (is_Some ((MkSeq.mapping seq) index)))
               /\ ((index >= (MkSeq.length seq))
                  <==> (is_None ((MkSeq.mapping seq) index))))

   type State 'item = seq: _State 'item{SeqSafety seq}

   val length:
      #item: Type
      -> seq: State item
      -> Tot nat
   let length 'item (seq: State 'item) = MkSeq.length seq

   let to_map seq = MkSeq.mapping seq

   type Index (#item_t: Type) (seq: State item_t) =
      index: nat{index < (length seq)}

   type Equals 'item (lhs: State 'item) (rhs: State 'item) =
      (FEq (to_map lhs) (to_map rhs))
      /\ ((length lhs) = (length rhs))

   val empty: #item: Type -> Tot (State item)
   let empty 'item = MkSeq 0 (fun _ -> None)

   val single: 'item -> Tot (State 'item)
   let single item = MkSeq 1 (Map.add Map.empty 0 item)

   let maybe_nth seq = to_map seq

   val nth:
      #item: Type
      -> seq: State item
      -> index: Index seq
      -> Tot item
   let nth 'item seq index =
      match maybe_nth seq index with
         | Some item ->
            item

   val last: (seq: State 'item{0 < length seq}) -> Tot (Index seq)
   let last seq = (length seq) - 1

   val prepend: 'item -> State 'item -> Tot (State 'item)
   let prepend item seq =
      MkSeq
         ((length seq) + 1)
         (fun index ->
            if index = 0 then
               Some item
            else
               maybe_nth seq (index - 1))

   val append: State 'item -> 'item -> Tot (State 'item)
   let append seq item =
      MkSeq
         ((length seq) + 1)
         (fun index ->
            if index = (length seq) then
               Some item
            else
               maybe_nth seq index)

   val insert:
      seq: State 'item
      -> ante: nat{ante <= length seq}
      -> 'item
      -> Tot (State 'item)
   let insert seq ante item =
      MkSeq
         ((length seq) + 1)
         (fun n ->
            if n = ante then
               Some item
            else if n < ante then
               maybe_nth seq n
            else
               maybe_nth seq (n - 1))

   val remove:
      #item_t: Type
      -> seq: State item_t{0 < length seq}
      -> index: Index seq
      -> Tot (State item_t)
   let remove (item_t: Type) seq index =
      MkSeq
         ((length seq) - 1)
         (fun n ->
            if n < index then
               maybe_nth seq n
            else
               maybe_nth seq (n + 1))

   val concat: State 'item -> State 'item -> Tot (State 'item)
   let concat lhs rhs =
      MkSeq
         ((length lhs) + (length rhs))
         (fun index ->
            if index < (length lhs) then
               maybe_nth lhs index
            else
               maybe_nth rhs (index - (length lhs)))

   val _foldl__loop:
      #item: Type
      -> #accum: Type
      -> seq: State item
      -> (accum -> Index seq -> Tot accum)
      -> accum
      -> index: Index seq
      -> Tot accum (decreases index)
   let rec _foldl__loop 'item 'accum seq fold accum index =
      if index = 0 then
         accum
      else
         _foldl__loop seq fold (fold accum index) (index - 1)

   val foldl:
      #item: Type
      -> #accum: Type
      -> seq: State item
      -> (accum -> index: Index seq -> Tot accum)
      -> accum
      -> Tot accum
   let foldl 'item 'accum seq fold accum =
      let len = length seq in
         if len = 0 then
            accum
         else
            _foldl__loop seq fold accum (len - 1)

   val filter:
      #item: Type
      -> (item -> Tot bool)
      -> State item
      -> Tot (State item)
   let filter 'item pred seq =
      foldl
         seq
         (fun (accum: State 'item) index ->
            let item = nth seq index in
               if pred item then
                  append accum item
               else
                  accum)
         empty

   val count: ('item -> Tot bool) -> State 'item -> Tot nat
   let count pred seq =
      foldl
         seq
         (fun (accum: nat) index ->
            if pred (nth seq index) then
               accum + 1
            else
               accum)
         0

   val map:
      #from_item: Type
      -> #to_item: Type
      -> (from_item -> Tot to_item)
      -> State from_item
      -> Tot (State to_item)
   let map 'from_item 'to_item xform from_seq =
      foldl
         from_seq
         (fun (accum: State 'to_item) index ->
            append accum (xform (nth from_seq index)))
         empty

   val maybe_find:
      #item: Type
      -> (item -> Tot bool)
      -> seq: State item
      -> Index seq
      -> Tot (option (Index seq))
   let maybe_find 'item pred seq start =
      foldl
         seq
         (fun (accum: option (Index seq)) index ->
            if index >= start then
               match accum with
                  | None ->
                     let item = nth seq index in
                        if pred item then
                           Some index
                        else
                           accum
                  | _ ->
                     accum
            else
               accum)
         None

   val find:
      #item: Type
      -> pred: (item -> Tot bool)
      -> seq: State item
      -> start: Index seq{is_Some (maybe_find pred seq start)}
      -> Tot (Index seq)
   let find 'item pred seq start =
      match maybe_find pred seq start with
         Some index ->
            index

   val slice:
      #item: Type
      -> seq: State item
      -> start: Index seq
      -> stop: nat{start <= stop && stop <= length seq}
      -> Tot (State item)
   let slice seq start stop =
      let length' = (stop - start) in
         MkSeq
            length'
            (fun i ->
               if i < length' then
                  (to_map seq) (i + start)
               else
                  None)

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
