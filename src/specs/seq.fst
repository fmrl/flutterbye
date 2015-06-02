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

module Tesseract.Specs.Seq

   type _spec_g (item_t: Type) =
      nat -> Tot (option item_t)

   type _seq_g (item_t: Type) 
      = 
         { 
            spec: _spec_g item_t;
            length: nat
         }

   type is_seq_safe: #item_t: Type -> spec: _spec_g item_t -> length: nat -> Type 
      =
         fun (item_t: Type) (spec: _spec_g item_t) (length: nat) ->
            forall (idx: nat).
               ((idx < length) <==> (is_Some (spec idx)))
               /\ ((idx >= length) <==> (None = (spec idx)))

   type seq_g (item_t: Type) 
      = seq: _seq_g item_t{is_seq_safe seq.spec seq.length}

   val bless:
      #item_t: Type ->
      spec: _spec_g item_t -> length: nat{is_seq_safe spec length} -> Tot (seq_g item_t)
   let bless spec length 
      =
         {
            spec = spec;
            length = length
         }

   val empty: #item_t: Type -> Tot (seq_g item_t)
   let empty (item_t: Type) 
      = bless (fun _ -> None) 0

   val single: 
      #item_t: Type -> 
      item_t -> Tot (seq_g item_t)
   let single item 
      =
         bless
            (fun idx ->
               if 0 = idx then
                  Some item
               else
                  None)
            1

   val length: 
      #item_t: Type -> 
      seq_g item_t -> Tot nat
   let length (item_t: Type) seq 
      = seq.length

   let to_map seq = seq.spec
   let lookup seq = seq.spec

   val nth: 
      #item_t: Type -> 
      seq: seq_g item_t -> idx: nat{idx < length seq} 
         -> Tot item_t
   let nth (item_t: Type) seq idx
      = 
         match lookup seq idx with
            | Some item ->
               item

   val first: 
      #item_t: Type -> 
         seq: seq_g item_t{0 < length seq} 
         -> Tot item_t
   let first (item_t: Type) seq 
      = nth seq 0

   val last: 
      #item_t: Type -> 
         seq: seq_g item_t{0 < length seq} 
         -> Tot item_t
   let last (item_t: Type) seq 
      = nth seq ((length seq) - 1)

   val append:
      #item_t: Type 
      -> seq_g item_t
      -> item_t
      -> Tot (seq_g item_t)
   let append (item_t: Type) seq item 
      =
         bless
            (fun idx -> 
               if idx = seq.length then 
                  Some item 
               else 
                  lookup seq idx)
            (seq.length + 1)

   val insert:
      #item_t: Type
      -> seq: seq_g item_t 
      -> before: nat{before <= length seq}
      -> item_t 
      -> Tot (seq_g item_t)
   let insert (item_t: Type) seq before item
      = 
         bless
            (fun n ->
               if n = before then
                  Some item
               else if n < before then
                  lookup seq n
               else
                  lookup seq (n - 1))
            (seq.length + 1)

   val remove:
      #item_t: Type
      -> seq: seq_g item_t{0 < length seq}
      -> idx: nat{idx < length seq}
      -> Tot (seq_g item_t)
   let remove (item_t: Type) seq idx 
      = 
         bless
            (fun n ->
               if n < idx then
                  lookup seq n
               else
                  lookup seq (n + 1))
            (seq.length - 1)

   val concat: 
      #item_t: Type
      -> seq_g item_t -> seq_g item_t
      -> Tot (seq_g item_t)
   let concat lhs rhs 
      =
         bless
            (fun idx ->
               if idx < lhs.length then
                  lhs.spec idx
               else
                  rhs.spec (idx - lhs.length))
            (lhs.length + rhs.length)

   val _foldl__loop: 
      #item_t: Type -> #accum_t: Type -> 
      seq: seq_g item_t -> (accum_t -> item_t -> Tot accum_t) 
         -> accum_t -> idx: nat{idx < length seq}
         -> Tot accum_t (decreases idx)
   let rec _foldl__loop (item_t: Type) (accum_t: Type) seq fn accum idx 
      = 
         if idx = 0 then
            accum
         else
            _foldl__loop seq fn (fn accum (nth seq idx)) (idx - 1)

   val foldl: 
      #item_t: Type -> #accum_t: Type 
      -> (accum_t -> item_t -> Tot accum_t) -> accum_t -> seq_g item_t 
      -> Tot accum_t
   let rec foldl (item_t: Type) (accum_t: Type) fn accum seq 
      = 
         let len = length seq in
            if 0 = len then
               accum
            else
               _foldl__loop seq fn accum (len - 1)

   val filter: 
      #item_t: Type
      -> (item_t -> Tot bool)
      -> seq_g item_t 
      -> Tot (seq_g item_t)
   let filter (item_t: Type) fn seq 
      =
         foldl
            (fun (a: seq_g item_t) e ->
               if fn e then
                  append a e
               else
                  a)
            Seq.empty
            seq

   val map:
      #item0_t: Type
      -> #item1_t: Type
      -> (item0_t -> Tot item1_t)
      -> seq_g item0_t
      -> Tot (seq_g item1_t)
   let map (item0_t: Type) (item1_t: Type) fn seq0
      = 
         foldl
            (fun (accum: seq_g item1_t) item ->
               Seq.append accum (fn item))
            Seq.empty
            seq0

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
