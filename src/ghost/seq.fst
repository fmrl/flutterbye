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

module Tesseract.Ghost.Seq

   type _seq 'lmnt = 
      { 
         maybe_nth: nat -> Tot (option 'lmnt);
         length: nat
      }

   type is_safe: #lmnt_t: Type -> _seq lmnt_t -> Type =
      fun (lmnt_t: Type)(sq: _seq lmnt_t) ->
         forall (idx: nat).
            ((idx < sq.length) <==> (is_Some (sq.maybe_nth idx)))
            /\ ((idx >= sq.length) <==> (None = (sq.maybe_nth idx)))

   type seq (lmnt_t: Type) = 
      sq: _seq lmnt_t{is_safe sq}

   val empty: #lmnt_t: Type -> Tot (seq lmnt_t)
   let empty (lmnt_t: Type) = 
      {
         maybe_nth = (fun _ -> (None <: option lmnt_t));
         length = 0
      }

   val length: #lmnt_t: Type -> seq lmnt_t -> Tot nat
   let length (lmnt_t: Type) sq = sq.length

   let maybe_nth sq = sq.maybe_nth

   val nth: #lmnt_t: Type -> sq: seq lmnt_t -> idx: nat{idx < length sq} -> Tot lmnt_t
   let nth (lmnt_t: Type) sq idx = 
      match maybe_nth sq idx with
         | Some e ->
            e

   val first: #lmnt_t: Type -> sq: seq lmnt_t{0 < length sq} -> Tot lmnt_t
   let first (lmnt_t: Type) sq =
      nth sq 0

   val last: #lmnt_t: Type -> sq: seq lmnt_t{0 < length sq} -> Tot lmnt_t
   let last (lmnt_t: Type) sq =
      nth sq ((length sq) - 1)

   val hd: #lmnt_t: Type -> sq: seq lmnt_t{0 < length sq} -> Tot lmnt_t
   let hd (lmnt_t: Type) sq = 
      nth sq 0
   let fst = hd

   val append: #lmnt_t: Type -> seq lmnt_t -> lmnt_t -> Tot (seq lmnt_t)
   let append (lmnt_t: Type) sq e =
      {
         maybe_nth = 
            (fun idx -> 
               if idx = sq.length then 
                  Some e 
               else 
                  maybe_nth sq idx);
         length = sq.length + 1
      }

   val _foldl__loop: 
      #lmnt_t: Type -> #acm_t: Type 
      -> sq:seq lmnt_t -> (acm_t -> lmnt_t -> Tot acm_t) -> acm_t -> idx:nat{idx < length sq}
      -> Tot acm_t (decreases idx)
   let rec _foldl__loop (lmnt_t: Type)(acm_t: Type) sq fn acm idx = 
      if idx = 0 then
         acm
      else
         _foldl__loop sq fn (fn acm (nth sq idx)) (idx - 1)

   val foldl: 
      #lmnt_t: Type -> #acm_t: Type 
      -> (acm_t -> lmnt_t -> Tot acm_t) -> acm_t -> seq lmnt_t 
      -> Tot acm_t
   let rec foldl (lmnt_t: Type) (acm_t: Type) fn acm sq = 
      let len = length sq in
         if 0 = len then
            acm
         else
            _foldl__loop sq fn acm (len - 1)

   val filter: 
      #lmnt_t: Type
      -> seq lmnt_t -> (lmnt_t -> Tot bool)
      -> Tot (seq lmnt_t)
   let filter (lmnt_t: Type) sq fn =
      foldl
         (fun (a: seq lmnt_t) e ->
            if fn e then
               append a e
            else
               a)
         Seq.empty
         sq

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
