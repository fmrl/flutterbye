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

//@requires "map.fst"

module Tesseract.Ghost.Seq

   type _spec_g (element_t: Type) =
      Map.map_g nat element_t

   type _seq_g (element_t: Type) = 
      { 
         spec: _spec_g element_t;
         length: nat
      }

   type is_seq_safe: #element_t: Type -> spec: _spec_g element_t -> length: nat -> Type =
      fun (element_t: Type) (spec: _spec_g element_t) (length: nat) ->
         forall (index: nat).
            ((index < length) <==> (is_Some (spec index)))
            /\ ((index >= length) <==> (None = (spec index)))

   (*type is_seq_safe: #element_t: Type -> _seq_g element_t -> Type =
      fun (element_t: Type) (seq: _seq_g element_t) ->
         forall (index: nat).
            ((index < seq.length) <==> (is_Some (seq.spec index)))
            /\ ((index >= seq.length) <==> (None = (seq.spec index)))*)

   type seq_g (element_t: Type) = 
      seq: _seq_g element_t{is_seq_safe seq.spec seq.length}

   val bless:
      #element_t: Type ->
      spec: _spec_g element_t -> length: nat{is_seq_safe spec length} -> Tot (seq_g element_t)
   let bless spec length =
      {
         spec = spec;
         length = length
      }

   val empty: #element_t: Type -> Tot (seq_g element_t)
   let empty (element_t: Type) = 
      bless (fun _ -> None) 0

   val single: 
      #element_t: Type -> 
      element_t -> Tot (seq_g element_t)
   let single lmnt =
      bless
         (fun index ->
            if 0 = index then
               Some lmnt
            else
               None)
         1

   val length: 
      #element_t: Type -> 
      seq_g element_t -> Tot nat
   let length (element_t: Type) seq = 
      seq.length

   let to_map seq = seq.spec
   let lookup seq = seq.spec

   val nth: 
      #element_t: Type -> 
      seq: seq_g element_t -> index: nat{index < length seq} 
         -> Tot element_t
   let nth (element_t: Type) seq index = 
      match lookup seq index with
         | Some lmnt ->
            lmnt

   val first: 
      #element_t: Type -> 
         seq: seq_g element_t{0 < length seq} 
         -> Tot element_t
   let first (element_t: Type) seq =
      nth seq 0

   val last: 
      #element_t: Type -> 
         seq: seq_g element_t{0 < length seq} 
         -> Tot element_t
   let last (element_t: Type) seq =
      nth seq ((length seq) - 1)

   val append: 
      #element_t: Type -> 
         seq_g element_t -> element_t -> Tot (seq_g element_t)
   let append (element_t: Type) seq lmnt =
      bless
         (fun index -> 
            if index = seq.length then 
               Some lmnt 
            else 
               lookup seq index)
         (seq.length + 1)

   val concat: 
      #element_t: Type
      -> seq_g element_t -> seq_g element_t
      -> Tot (seq_g element_t)
   let concat lhs rhs =
      bless
         (fun index ->
            if index < lhs.length then
               lhs.spec index
            else
               rhs.spec (index - lhs.length))
         (lhs.length + rhs.length)

   val _foldl__loop: 
      #element_t: Type -> #accum_t: Type -> 
      seq: seq_g element_t -> (accum_t -> element_t -> Tot accum_t) 
         -> accum_t -> index: nat{index < length seq}
         -> Tot accum_t (decreases index)
   let rec _foldl__loop (element_t: Type) (accum_t: Type) seq fn accum index = 
      if index = 0 then
         accum
      else
         _foldl__loop seq fn (fn accum (nth seq index)) (index - 1)

   val foldl: 
      #element_t: Type -> #accum_t: Type 
      -> (accum_t -> element_t -> Tot accum_t) -> accum_t -> seq_g element_t 
      -> Tot accum_t
   let rec foldl (element_t: Type) (accum_t: Type) fn accum seq = 
      let len = length seq in
         if 0 = len then
            accum
         else
            _foldl__loop seq fn accum (len - 1)

   val filter: 
      #element_t: Type
      -> seq_g element_t -> (element_t -> Tot bool)
      -> Tot (seq_g element_t)
   let filter (element_t: Type) seq fn =
      foldl
         (fun (a: seq_g element_t) e ->
            if fn e then
               append a e
            else
               a)
         Seq.empty
         seq

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
