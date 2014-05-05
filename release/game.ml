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
          if roll_num = cROLL_ROBBER then (None, s') (* Do nothing for now *)
            let new_robber_loc = Random.int cMAX_PIECE_NUM in
            (* TODO: Discard if over cMAX_HAND_SIZE *)
            let active_color = turn.active in
            let hex_corners = Util.piece_corners new_robber_loc in
            let settlements = fst (snd board) in
            let rec adjacent_settlement_color corners = match corners with
              (* Loop through all corner tiles *)
              (* Try to find settlements at those corners *)
              (* If there is a settlement, look at the color of the settlement *)
              (* If not the same as the current color, return that color *)
              (* If nothing found, return None *)
              | h::t -> match List.nth h with
                | None -> adjacent_settlement_color t
                | Some (color, stlmt) -> if color <> active_color then Some color else adjacent_settlement_color t
              | [] -> None
            in let adj_color = adjacent_settlement_color hex_corners in
            (* Rob target player *)
            let rec rob_player plist = match plist with (* Take resource from chosen player *)
              | h::t -> let (clr, ((b, w, o, g, l), crds), trophs) = h in
                if clr <> adj_color then rob_player t else
                (* Tuple with cost, and an option saying if something was able to be robbed *)
                if b > 0 then ((b - 1, w, o, g, l), Some Brick)
                else if w > 0 then ((b, w - 1, o, g, l), Some Wool)
                else if o > 0 then ((b, w, o - 1, g, l), Some Ore)
                else if g > 0 then ((b, w, o, g - 1, l), Some Grain)
                else if l > 0 then ((b, w, o, g, l - 1), Some Lumber)
                else ((b, w, o, g, l), None)
              | [] -> failwith "No player found for color"
            in let rob_result = rob_player player_list in (* Tuple of robbed results and the type that was robbed *)
            (* Benefit current player *)
            let rec reap_robber_rewards plist = match plist with (* Add taken resource to current player *)
              | h::t -> let (clr, ((b, w, o, g, l), crds), trophs) = h in
                if clr <> active_color then rob_player t else
                match (snd rob_result) with
                | None -> (b, w, o, g, l) (* Nothing could be robbed *)
                | Some Brick -> (b + 1, w, o, g, l)
                | Some Wool -> (b, w + 1, o, g, l)
                | Some Ore -> (b, w, o + 1, g, l)
                | Some Grain -> (b, w, o, g + 1, l)
                | Some Lumber -> (b, w, o, g, l + 1)
              | [] -> failwith "Player for current color couldn't be found"
            in let reap_result = reap_robber_rewards player_list in (* Robbed resource added to current player's resources *)
            (* Generate new state *)
            let rec recreate_player_list plist acc = match plist with
              | h::t -> let (clr, (invtr, crds), trophs) = h in
                if clr <> active_color && clr <> adj_color then recreate_player_list t (h::acc) (* Add current player to new list *)
                else if clr = active_color then recreate_player_list t ((clr, (reap_result, crds), trophs)::acc) (* Add current player to new list *)
                else if clr = adj_color then recreate_player_list t ((clr, ((fst rob_result), crds), trophs)::acc) (* Add robbed player to new list *)
                else failwith "Something wrong with player list and colors"
              | [] -> List.rev acc (* Everything had been reversed in accumulator, so reversing to get it back *)
            in let new_player_list = recreate_player_list player_list [] in
            (None, (board, new_player_list, turn, (color, curr_req))) (* No one wins, but update state *)
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
