open Definition
open Constant
open Util
open Print


type game = state

let state_of_game g = g
let game_of_state s = s

let rec build_settlement_at_point curr_intersections clr stlmt p index acc = 
  match curr_intersections with
  | h::t -> 
    if p = index 
    then (build_settlement_at_point t clr stlmt p (index + 1) ((color, stlmt) :: acc)) 
    else (build_settlement_at_point t clr stlmt p (index + 1) (None :: acc))
  | [] -> List.rev acc


let init_game () = game_of_state (gen_initial_state())


let handle_move s m = let (board, player_list, turn, (color, curr_req)) = s in
  Random.self_init ();
  let rec handle_move_helper s' m' = (* Recursive so we can sub in a move for invalid moves *)
    match curr_req with
    | InitialRequest ->
      match m' with 
      | InitialMove (p1, p2) -> (* TODO: Check if p1 is too close to existing settlement *)
        let pt = if (p1 > cMAX_POINT_NUM) || (p1 < cMIN_POINT_NUM) then Random.int cMAX_POINT_NUM else p1 in
        let (map, (curr_intrs, curr_roads), deck, disc, robber) = board in
        let structures = (build_settlement_at_point curr_intrs color Town pt 0 []) in
        let road = (color, (pt, p2)) in
        let new_board = (map, (structures, (road::curr_roads)), deck, disc, robber) in
        (None, (new_board, player_list, turn, (color, curr_req)))
      | _ -> failwith "Fill in valid moves"
    | RobberRequest ->
      match m' with
      | RobberMove rm ->
      | _ -> failwith "Fill in valid moves"
    | DiscardRequest ->
      match m' with
      | DiscardMove (cost_b, cost_w, cost_o, cost_g, cost_l) ->
      | _ -> failwith "Fill in valid moves"
    | TradeRequest ->
      | TradeResponse b ->
      | _ -> failwith "Fill in valid moves"
    | ActionRequest -> 
      match m' with
      | Action a ->
        match a with
        | RollDice -> let roll_num = Util.random_roll () in
          if roll_num = cROLL_ROBBER
          then (None, s') (* Do nothing for now *)
          else 
            let new_turn = {  (* Update turn with roll number *)
              active = turn.active;
              dicerolled = Some roll_num;
              cardplayed = turn.cardplayed;
              cardsbought = turn.cardsbought;
              tradesmade = turn.tradesmade;
              pendingtrade = turn.pendingtrade
            } in (* TODO: Do resources get generated as part of this move or the next one? *)
            (None, (board, player_list, new_turn, (color, curr_req)))
        | MaritimeTrade (resource1, resource2) -> failwith "Not yet"
        | DomesticTrade (color, cost1, cost2) -> failwith "Not yet"
        | BuyBuild b -> failwith "Not yet"
        | PlayCard pc -> failwith "Not yet"
        | EndTurn -> 
            match turn.dicerolled with
            | Some _ -> (None, s') (* Nothing changed so end turn *)
            (* If no dice has been rolled, substitute dice roll move because dice roll is required for turn *)
            | None -> handle_move_helper (board, player_list, turn, (color, ActionRequest)) (Action RollDice)
      | _ -> (None, s') (* Action end turn *)
  in handle_move_helper s m

let presentation s = failwith "Were not too much to pay for birth."
