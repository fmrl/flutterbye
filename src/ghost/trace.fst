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

//@requires "seq.fst"

module Tesseract.Ghost.Trace

   type step_fn (ev_t: Type) (st_t: Type) = 
      ev_t -> st_t -> Tot st_t

   type _trace (ev_t: Type) (st_t: Type) =
      {
         log: Seq.seq (ev_t * st_t);
         step: step_fn ev_t st_t;
         initst: st_t
      }

   type is_safe: #ev_t: Type -> #st_t: Type -> _trace ev_t st_t -> Type =
      fun (ev_t: Type) (st_t: Type) (tr: _trace ev_t st_t) ->
         // empty logs are safe.
         (0 = (Seq.length tr.log))
         // the first entry of the log must be the result of the first event applied to the initialization state.
         \/ ((match Seq.nth tr.log 0 with
               | (e, s') ->
                  s' = tr.step e tr.initst)
            // all remaining steps are derived similarly from the state in the previous log entry.
            /\ (forall i.
                  0 < i && i < (Seq.length tr.log)
                  ==>
                     (match Seq.nth tr.log (i - 1) with
                        | (_, s) ->
                           match Seq.nth tr.log i with
                              | (e, s') ->
                                 s' = tr.step e s)))

   type trace (ev_t: Type) (st_t: Type) =
      tr: _trace ev_t st_t{is_safe tr}

   val new: #ev_t: Type -> #st_t: Type -> step_fn ev_t st_t -> st_t -> Tot (trace ev_t st_t)
   let new (ev_t: Type) (st_t: Type) fn st0 = 
      {
         log = Seq.empty;
         step = fn;
         initst = st0
      }

   val log: #ev_t: Type -> #st_t: Type -> trace ev_t st_t -> Tot (Seq.seq (ev_t * st_t))
   let log (ev_t: Type) (st_t: Type) trc =
      trc.log

   val initst: #ev_t: Type -> #st_t: Type -> trace ev_t st_t -> Tot st_t
   let initst (ev_t: Type) (st_t: Type) tr =
      tr.initst
   
   val curst: #ev_t: Type -> #st_t: Type -> trace ev_t st_t -> Tot st_t
   let curst (ev_t: Type) (st_t: Type) tr =
      if 0 = Seq.length (log tr) then
         initst tr
      else
         match Seq.last (log tr) with
            | (_, s) ->
               s

   val now: #ev_t: Type -> #st_t: Type -> trace ev_t st_t -> Tot st_t
   let now (ev_t: Type) (st_t: Type) tr =
      if 0 = Seq.length tr.log then
         initst tr
      else
         match Seq.last tr.log with
            | (_, s) ->
               s

   val step: #ev_t: Type -> #st_t: Type -> trace ev_t st_t -> ev_t -> Tot (trace ev_t st_t)
   let step (ev_t: Type) (st_t: Type) tr ev =
      let 
         state =
            // todo: f* doesn't see that s = Seq.empty <==> 0 = Seq.length s. 
            // this seems like a good opportunity for a lemma related to Seq.empty.
            // todo: would functional extensionality help somehow here?
            //if tr.log = Seq.empty then
            if 0 = Seq.length tr.log then
               tr.initst
            else
               match Seq.last tr.log with
                  | (_, s) ->
                     s
      in
         {
            log = Seq.append tr.log (ev, tr.step ev state);
            step = tr.step;
            initst = tr.initst
         }

// $vim-fst:32: vim:set sts=3 sw=3 et ft=fstar:,$
