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

   type _seq_g (item_t: Type) 
      = { 
         map: Map.map_g nat item_t;
         length: nat
      }

   type _is_seq_safe: #item_t: Type -> seq: _seq_g item_t -> Type 
      = fun (item_t: Type) (seq: _seq_g item_t) 
         -> ((0 = seq.length) 
               /\ (FunctionalExtensionality.FEq seq.map (fun _ -> None)))
            \/ (forall (index: nat).
                  ((index < seq.length) <==> (is_Some (seq.map index)))
                  /\ ((index >= seq.length) <==> (is_None (seq.map index))))

   type seq_g (item_t: Type) 
      = seq: _seq_g item_t{_is_seq_safe seq}

   type index_g (#item_t: Type) (seq: seq_g item_t) 
      = index: nat{index < seq.length}

   type are_equal 
      (#item_t: Type) 
      (lhs: seq_g item_t) 
      (rhs: seq_g item_t)
      = (FunctionalExtensionality.FEq lhs.map rhs.map) 
         /\ (lhs.length = rhs.length)

   val empty: #item_t: Type -> Tot (seq_g item_t)
   let empty (item_t: Type) 
      = {
         map = (fun _ -> None);
         length = 0
      }

   val length: 
      #item_t: Type 
      -> seq: seq_g item_t
      -> Tot nat
   let length (item_t: Type) (seq: seq_g item_t)
      = seq.length

   val single: #item_t: Type -> item_t -> Tot (seq_g item_t)
   let single item 
      = {
         map = Map.add Map.empty 0 item;
         length = 1
      }

   let maybe_nth seq = seq.map
   let to_map seq = seq.map

   val nth: 
      #item_t: Type 
      -> seq: seq_g item_t 
      -> index: index_g seq
      -> Tot item_t
   let nth (item_t: Type) seq index
      = 
         match maybe_nth seq index with
            | Some item ->
               item

   val last: 
      #item_t: Type 
      -> seq: seq_g item_t{0 < length seq} 
      -> Tot (index_g seq)
   let last (item_t: Type) seq 
      = (length seq) - 1

   val append:
      #item_t: Type 
      -> seq_g item_t
      -> item_t
      -> Tot (seq_g item_t)
   let append (item_t: Type) seq item 
      = {
         map =
            (fun index -> 
               if index = seq.length then 
                  Some item 
               else 
                  maybe_nth seq index);
         length = (seq.length + 1)
      }

   val insert:
      #item_t: Type
      -> seq: seq_g item_t 
      -> before: nat{before <= length seq}
      -> item_t 
      -> Tot (seq_g item_t)
   let insert (item_t: Type) seq before item
      = {
         map =
            (fun n ->
               if n = before then
                  Some item
               else if n < before then
                  maybe_nth seq n
               else
                  maybe_nth seq (n - 1));
         length = (seq.length + 1)
      }

   val remove:
      #item_t: Type
      -> seq: seq_g item_t{0 < length seq}
      -> index: index_g seq
      -> Tot (seq_g item_t)
   let remove (item_t: Type) seq index 
      = {
         map =
            (fun n ->
               if n < index then
                  maybe_nth seq n
               else
                  maybe_nth seq (n + 1));
         length = (seq.length - 1)
      }

   val concat: 
      #item_t: Type
      -> seq_g item_t 
      -> seq_g item_t
      -> Tot (seq_g item_t)
   let concat lhs rhs 
      = {
         map =
            (fun index ->
               if index < lhs.length then
                  maybe_nth lhs index
               else
                  maybe_nth rhs (index - lhs.length));
         length =
            (lhs.length + rhs.length)
      }

   val _foldl__loop: 
      #item_t: Type 
      -> #accum_t: Type 
      -> seq: seq_g item_t 
      -> (accum_t -> index_g seq -> Tot accum_t) 
      -> accum_t 
      -> index: index_g seq
      -> Tot accum_t (decreases index)
   let rec _foldl__loop (item_t: Type) (accum_t: Type) seq fold accum index 
      =  if index = 0 then
            accum
         else
            _foldl__loop seq fold (fold accum index) (index - 1)

   val foldl: 
      #item_t: Type 
      -> #accum_t: Type 
      -> seq: seq_g item_t 
      -> (accum_t -> index: index_g seq -> Tot accum_t) 
      -> accum_t 
      -> Tot accum_t
   let foldl (item_t: Type) (accum_t: Type) seq fold accum 
      =  let len = length seq in
         if len = 0 then
            accum
         else
            _foldl__loop seq fold accum (len - 1)

   val filter: 
      #item_t: Type
      -> (item_t -> Tot bool)
      -> seq_g item_t 
      -> Tot (seq_g item_t)
   let filter (item_t: Type) pred seq 
      = 
         foldl
            seq
            (fun (accum: seq_g item_t) index ->
               let item = nth seq index in
                  if pred item then
                     append accum item
                  else
                     accum)
            empty

   val map:
      #item0_t: Type
      -> #item1_t: Type
      -> (item0_t -> Tot item1_t)
      -> seq_g item0_t
      -> Tot (seq_g item1_t)
   let map (item0_t: Type) (item1_t: Type) xform seq0
      =  
         foldl
            seq0
            (fun (accum: seq_g item1_t) index ->
               append accum (xform (nth seq0 index)))
            empty

   val maybe_find:
      #item_t: Type
      -> (item_t -> Tot bool)
      -> seq: seq_g item_t
      -> index_g seq
      -> Tot (option (index_g seq))
   let maybe_find (item_t: Type) pred seq start
      =  
         foldl
            seq
            (fun (accum: option (index_g seq)) index ->
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
      #item_t: Type
      -> pred: (item_t -> Tot bool)
      -> seq: seq_g item_t
      -> start: index_g seq{is_Some (maybe_find pred seq start)}
      -> Tot (index_g seq)
   let find (item_t: Type) pred seq start
      = match maybe_find pred seq start with
         Some index ->
            index

   val _slice:
      #item_t: Type
      -> seq: seq_g item_t
      -> start: index_g seq
      -> end_: nat{start <= end_ && end_ < Seq.length seq}
      -> Tot (_seq_g item_t)
   let _slice seq start end_
      = {
         map = 
            (fun i -> 
               seq.map (i + start));
         length = end_ - start
      }

   val __slice_safety_properties:
      #item_t: Type
      -> seq: seq_g item_t
      -> start: index_g seq
      -> end_: nat{start <= end_ && end_ < Seq.length seq}
      -> Lemma
         (ensures (_is_seq_safe (_slice seq start end_)))
   let __slice_safety_properties seq start end_
      = admit ()

   val slice:
      #item_t: Type
      -> seq: seq_g item_t
      -> start: index_g seq
      -> end_: nat{start <= end_ && end_ < Seq.length seq}
      -> Tot (seq_g item_t)
   let slice seq start end_
      = __slice_safety_properties seq start end_;
         _slice seq start end_

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
