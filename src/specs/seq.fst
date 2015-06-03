// $legal:322:
// 
// This work is licensed under the Creative Commons
// Attribution-NonCommercial-ShareAlike 4.0 International
// License. To view a copy of this license, visit
// http://creativecommons.org/licenses/by-nc-sa/4.0/
// or send a letter to:
// 
// Creative Commons
// PO Box 1866
// Mountain View, CA 94042
// USA
// 
// ,$

//@requires "fstar:ext.fst"

module Tesseract.Specs.Seq

   type _seq_g (item_t: Type) 
      = { 
         maybe_nth: nat -> Tot (option item_t);
         length: nat
      }

   type is_seq_safe: #item_t: Type -> seq: _seq_g item_t -> Type 
      = fun (item_t: Type) (seq: _seq_g item_t) 
         -> ((0 = seq.length) 
               /\ (FunctionalExtensionality.FEq seq.maybe_nth (fun _ -> None)))
            \/ (forall (index: nat).
                  ((index < seq.length) <==> (is_Some (seq.maybe_nth index)))
                  /\ ((index >= seq.length) <==> (is_None (seq.maybe_nth index))))

   type seq_g (item_t: Type) 
      = seq: _seq_g item_t{is_seq_safe seq}

   type index_g (#item_t: Type) (seq: seq_g item_t) 
      = index: nat{index < seq.length}

   type are_equal 
      (#item_t: Type) 
      (lhs: seq_g item_t) 
      (rhs: seq_g item_t)
      = (FunctionalExtensionality.FEq lhs.maybe_nth rhs.maybe_nth) 
         /\ (lhs.length = rhs.length)

   val empty: #item_t: Type -> Tot (seq_g item_t)
   let empty (item_t: Type) 
      = {
         maybe_nth = (fun _ -> None);
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
         maybe_nth = 
            (fun index ->
               if 0 = index then
                  Some item
               else
                  None);
         length = 1
      }

   let to_map seq = seq.maybe_nth
   let lookup seq = seq.maybe_nth

   val nth: 
      #item_t: Type 
      -> seq: seq_g item_t 
      -> index: index_g seq
      -> Tot item_t
   let nth (item_t: Type) seq index
      = 
         match lookup seq index with
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
         maybe_nth =
            (fun index -> 
               if index = seq.length then 
                  Some item 
               else 
                  lookup seq index);
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
         maybe_nth =
            (fun n ->
               if n = before then
                  Some item
               else if n < before then
                  lookup seq n
               else
                  lookup seq (n - 1));
         length = (seq.length + 1)
      }

   val remove:
      #item_t: Type
      -> seq: seq_g item_t{0 < length seq}
      -> index: index_g seq
      -> Tot (seq_g item_t)
   let remove (item_t: Type) seq index 
      = {
         maybe_nth =
            (fun n ->
               if n < index then
                  lookup seq n
               else
                  lookup seq (n + 1));
         length = (seq.length - 1)
      }

   val concat: 
      #item_t: Type
      -> seq_g item_t 
      -> seq_g item_t
      -> Tot (seq_g item_t)
   let concat lhs rhs 
      = {
         maybe_nth =
            (fun index ->
               if index < lhs.length then
                  lhs.maybe_nth index
               else
                  rhs.maybe_nth (index - lhs.length));
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

   val _foldl: 
      #item_t: Type 
      -> #accum_t: Type 
      -> seq: seq_g item_t 
      -> (accum_t -> index_g seq -> Tot accum_t) 
      -> accum_t 
      -> Tot accum_t
   let rec _foldl (item_t: Type) (accum_t: Type) seq fold accum 
      =  let len = length seq in
         if len = 0 then
            accum
         else
            _foldl__loop seq fold accum (len - 1)

   val foldl: 
      #item_t: Type 
      -> #accum_t: Type 
      -> (accum_t -> item_t -> Tot accum_t) 
      -> accum_t 
      -> seq_g item_t 
      -> Tot accum_t
   let rec foldl (item_t: Type) (accum_t: Type) fold accum seq 
      =  let len = length seq in
         let adaptor  = (fun accum index -> fold accum (nth seq index)) in
         _foldl seq adaptor accum 

   val filter: 
      #item_t: Type
      -> (item_t -> Tot bool)
      -> seq_g item_t 
      -> Tot (seq_g item_t)
   let filter (item_t: Type) pred seq 
      =  _foldl
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
      =  _foldl
            seq0
            (fun (accum: seq_g item1_t) index ->
               append accum (xform (nth seq0 index)))
            empty

   val maybe_find:
      #item_t: Type
      -> (item_t -> Tot bool)
      -> seq: seq_g item_t
      -> index_g seq
      -> Tot (option nat)
   let maybe_find (item_t: Type) pred seq start
      =  _foldl
            seq
            (fun (accum: option nat) index ->
               if index >= start then
                  match accum with
                     | None ->
                        if pred (nth seq index) then
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
      -> Tot (option nat)
   let find (item_t: Type) pred seq start
      =  _foldl
            seq
            (fun (accum: option nat) index ->
               if index >= start then
                  match accum with
                     | None ->
                        if pred (nth seq index) then
                           Some index
                        else
                           accum
                     | _ ->
                        accum
               else
                  accum)
            None

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
