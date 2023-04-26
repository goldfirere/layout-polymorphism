(* WG 2.8 2023 presentation on Abstract Templates *)

type point = { x : float; y : float }
type weighted_point = { x : float; y : float; weight : int }

(* pre-condition: sum of weights is not 0 *)
let center_of_gravity (pts : weighted_point array) : point =
  let {x; y; weight} = Array.fold_left
    (fun { x = x_acc; y = y_acc; weight = weight_acc } { x; y; weight } ->
      { x = x_acc +. x *. float_of_int weight
      ; y = y_acc +. y *. float_of_int weight
      ; weight = weight_acc + weight })
    { x = 0.0; y = 0.0; weight = 0 }
    pts
  in
  { x = x /. float_of_int weight; y = y /. float_of_int weight }
