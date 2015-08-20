(*--build-config
--*)

module Tesseract.Specs.Alt.Option

   val get: o: option 'a{is_Some o} -> Tot 'a
   let get o =
      match o with
         | Some a ->
            a
