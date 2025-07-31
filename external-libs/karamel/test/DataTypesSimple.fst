module DataTypesSimple

open FStar.HyperStack.ST

type t = | Cons1 | Cons2

type point = | Point2D: x:UInt32.t -> y:UInt32.t -> point

let magnitude = function
  | Point2D x y ->
      FStar.UInt32.(x *%^ x +%^ y *%^ y)

let f (): Stack t (fun _ -> true) (fun _ _ _ -> true) =
  Cons1

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let x = Cons1, Cons2 in
  let y = Point2D 0ul 1ul in
  let z = match f () with
    | Cons1 -> 0ul
    | Cons2 -> 1ul
  in
  pop_frame ();
  C.EXIT_SUCCESS
