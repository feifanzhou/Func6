open Definition
open Constant
open Util
open Print


type game = state

let state_of_game g = g
let game_of_state s = s


let init_game () = game_of_state (gen_initial_state())


let handle_move s m = failwith "If all the soul-and-body scars"

let presentation s = failwith "Were not too much to pay for birth."
