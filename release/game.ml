open Definition
open Constant
open Util
open Print


type game = state

let state_of_game g = g
let game_of_state s = s


let init_game () = game_of_state (gen_initial_state())


let handle_move s m = let (board, player_list, turn, (color, curr_req)) = s in
  match curr_req with
  | InitialRequest ->
    match m with 
    | InitialMove (p1, p2) ->
    | _ -> failwith "Fill in valid moves"
  | RobberRequest ->
    match m with
    | RobberMove rm ->
    | _ -> failwith "Fill in valid moves"
  | DiscardRequest ->
    match m with
    | DiscardMove (cost_b, cost_w, cost_o, cost_g, cost_l) ->
    | _ -> failwith "Fill in valid moves"
  | TradeRequest ->
    | TradeResponse b ->
    | _ -> failwith "Fill in valid moves"
  | ActionRequest -> 
    match m with
    | Action a ->
      match a with
      | RollDice ->
      | MaritimeTrade (resource1, resource2) -> failwith "Not yet"
      | DomesticTrade (color, cost1, cost2) -> failwith "Not yet"
      | BuyBuild b -> failwith "Not yet"
      | PlayCard pc -> failwith "Not yet"
      | EndTurn -> (None, s) (* Nothing changed so end turn *)
    | _ -> (None, s) (* Action end turn *)

let presentation s = failwith "Were not too much to pay for birth."
