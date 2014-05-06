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

let rec get_current_player plist active_color = match plist with
  | (clr, hnd, troph)::t -> if clr = active_color then (clr, hnd, troph) else get_current_player t
  | [] -> failwith "Couldn't find player for a color. Weird."

let rec update_player_inventory plist new_inventory active_color acc = match plist with
  | (clr, hnd, troph)::t -> 
    if clr = active_color (* Is discarding player, update inventory in player list *)
    then update_player_inventory t ((clr, (new_inventory, curr_cards), troph)::acc)
    else update_player_inventory t ((clr, hnd, troph)::acc)  (* Just put same entry back in *)
  | [] -> List.rev acc (* Maintain player list order *)


let init_game () = game_of_state (gen_initial_state())


let handle_move s m =
  Random.self_init ();
  let rec handle_move_helper s' m' = (* Recursive so we can sub in a move for invalid moves *)
    let (board, player_list, turn, (color, curr_req)) = s' in
    match curr_req with
    | InitialRequest ->
      match m' with 
      | InitialMove (p1, p2) -> (* TODO: Check if p1 is too close to existing settlement *)
        let pt = if (p1 > cMAX_POINT_NUM) || (p1 < cMIN_POINT_NUM) then Random.int cMAX_POINT_NUM else p1 in
        let (map, (curr_intrs, curr_roads), deck, disc, robber) = board in
        let structures = (build_settlement_at_point curr_intrs color Town pt 0 []) in
        let road = (color, (pt, p2)) in
        let new_board = (map, (structures, (road::curr_roads)), deck, disc, robber) in
        (* TODO: Determine what next request should be *)
        (None, (new_board, player_list, turn, (color, curr_req)))
      | _ -> failwith "Fill in valid moves"
    | RobberRequest ->
      match m' with
      | RobberMove (pt, adj_color) ->
        (* Rob target player *)
        let rec rob_player plist target_color = match plist with (* Take resource from chosen player *)
          | h::t -> let (clr, ((b, w, o, g, l), crds), trophs) = h in
            if clr <> target_color then rob_player t target_color else
            (* Tuple with cost, and an option saying if something was able to be robbed *)
            if b > 0 then ((b - 1, w, o, g, l), Some Brick)
            else if w > 0 then ((b, w - 1, o, g, l), Some Wool)
            else if o > 0 then ((b, w, o - 1, g, l), Some Ore)
            else if g > 0 then ((b, w, o, g - 1, l), Some Grain)
            else if l > 0 then ((b, w, o, g, l - 1), Some Lumber)
            else ((b, w, o, g, l), None)
          | [] -> rob_player player_list (next_turn clr) (* Try to rob someone else *)
        in let rob_result = rob_player player_list adj_color in (* Tuple of robbed results and the type that was robbed *)
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
        let (mp, str, dk, trash, rbr) = board in
        let new_board = (mp, str, dk, trash, pt) in (* Update robber position *)
        (None, (new_board, new_player_list, turn, (color, ActionRequest))) (* No one wins, but update state *)
      | _ -> failwith "Fill in valid moves"
    | DiscardRequest ->
      (* TODO: If resources < threshold, pass to next player *)
      let rec get_current_player_resource_count plist = match plist with
        | (clr, (curr_inv, curr_cards), troph)::t -> 
          if clr <> color
          then get_current_player_resource_count t
          else sum_cost curr_inv (* Found target player, getting sum of resources *)
        | [] -> failwith "Couldn't find requested player color. Weird"
      in let curr_resource_count = get_current_player_resource_count player_list in
      if curr_resource_count <= cMAX_HAND_SIZE (* No need to discard, try next player *)
      then (None, (board, player_list, turn, ((next_turn color), DiscardRequest)))
      else (* Current player needs to discard *)
        match m' with
        | DiscardMove (cost_b, cost_w, cost_o, cost_g, cost_l) ->
          let (curr_clr, (curr_inv, curr_cards), curr_troph) = get_current_player player_list color in
          let (curr_b, curr_w, curr_o, curr_g, curr_l) = curr_inv in
          (* TODO: Error checking — differences shouldn't be negative for example *)
          let new_inventory = (curr_b - cost_b, curr_w - cost_w, curr_o - cost_o, curr_g - cost_g, curr_l - cost_l) in
          let new_player_list = update_player_inventory player_list new_inventory color [] in
          if color <> White (* Not last player in order, get next one to try discarding resources *)
          then (None, (board, new_player_list, turn, ((next_turn color), DiscardRequest)))
          else (None, (board, new_player_list, turn, (turn.active, RobberRequest))) (* Pass control back to active player with RobberRequest *)
        | _ -> failwith "Fill in valid moves"
    | TradeRequest ->
      | TradeResponse b ->
      | _ -> failwith "Fill in valid moves"
    | ActionRequest -> 
      match m' with
      | Action a ->
        match a with
        | RollDice -> let roll_num = Util.random_roll () in
          let rolled_turn = {
            active: turn.active;
            dicerolled: Some roll_num;
            cardplayed: turn.cardplayed;
            cardsbought: turn.cardsbought;
            tradesmade: turn.tradesmade;
            pendingtrade: turn.pendingtrade;
          } in
          if roll_num = cROLL_ROBBER then
            let new_robber_loc = Random.int cMAX_PIECE_NUM in
            (* Discard if anyone is over cMAX_HAND_SIZE *)
            let rec who_is_over_max_hand_size plist acc = match plist with
              | h::t -> let (clr, (invtr, crds), trophs) = h in
                if Util.sum_cost invtr > cMAX_HAND_SIZE then ((true, Some clr)::acc) else is_over_max_hand_size t
              | [] -> List.rev acc (* Keep everything in order *)
            in let hogs = who_is_over_max_hand_size player_list in
            if List.length hogs > 0 then (* Some people have too many resources *)
              (* Someone has too many resources *)
              let first_hoarder_color = match List.hd hogs with
                | (b, Some c) -> c
                | _ -> failwith "Inconsistent results for hoaders"
              in (None, (board, player_list, rolled_turn, (first_hoarder_color, DiscardRequest))) (* Send discard request *)
            else 
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
              (None, (board, player_list, rolled_turn, (color, RobberRequest)))
          else (* Didn't roll robber *)
            (* TODO: Do resources get generated as part of this move or the next one? *)
            (None, (board, player_list, rolled_turn, (color, ActionRequest)))
        | MaritimeTrade (resource1, resource2) -> failwith "Not yet"
        | DomesticTrade (color, cost1, cost2) -> failwith "Not yet"
        | BuyBuild b -> failwith "Not yet"
        | PlayCard pc -> match pc with
            (* TODO: Something about knights and army size? *)
          | PlayKnight (rbrmv) -> handle_move_helper (board, player_list, turn, (color, RobberRequest)) (RobberMove(rbrmv))
          | PlayRoadBuilding (rd, rdopt) ->
            let (mp, (intrs, rds), dk, dsc, rbr) = board in
            let roads_to_add = match rdopt with
              | None -> [rd]
              | Some (other_road) -> [rd, other_road]
            in let new_roads = List.append rds roads_to_add in
            (None, (board, player_list, turn, (color, ActionRequest)))
          | PlayYearOfPlenty (rsrc, rsrcopt) -> 
            let (curr_clr, (curr_inv, curr_cards), curr_troph) = get_current_player player_list color in
            let update_inventory_for_type inv rsrc' = 
              let (curr_b, curr_w, curr_o, curr_g, curr_l) = inv in
              match rsrc' with
              | Brick -> (curr_b + 1, curr_w, curr_o, curr_g, curr_l)
              | Wool -> (curr_b, curr_w + 1, curr_o, curr_g, curr_l)
              | Ore -> (curr_b, curr_w, curr_o + 1, curr_g, curr_l)
              | Grain -> (curr_b, curr_w, curr_o, curr_g + 1, curr_l)
              | Lumber -> (curr_b, curr_w, curr_o, curr_g, curr_l + 1)
            in let inv' = update_inventory_for_type curr_inv rsrc in
            (* Update inventory for second type if one exists *)
            let final_inv = match rsrcopt with
              | None -> inv'
              | Some (res') -> update_inventory_for_type inv' res'
            (* Put player list back together *)
            let new_player_list = update_player_inventory player_list final_inv color [] in
            (None, (board, new_player_list, turn, (color, ActionRequest)))
          | PlayMonopoly (res) ->
            let rec take_resources plist acc monopoly_count = match plist with  (* New player list, count of resource *)
              | (clr, (curr_inv, curr_cards), troph)::t -> if clr = color then take_resources t acc monopoly_count else
                let (cb, cw, co, cg, cl) = curr_inv in
                let (new_inventory, curr_res_count) = match res with
                  | Brick -> ((0, cw, co, cg, cl), cb)
                  | Wool -> ((cb, 0, co, cg, cl), cw)
                  | Ore -> ((cb, cw, 0, cg, cl), co)
                  | Grain -> ((cb, cw, co, 0, cl), cg)
                  | Lumber -> ((cb, cw, co, cg, 0), cl)
                in let new_player = (clr, (new_inventory, curr_cards), troph) in
                take_resources t (new_player::acc) (monopoly_count + curr_res_count)
              | [] -> ((List.rev acc), monopoly_count)
            in let (ruined_players, spoils) = take_resources player_list [] 0 in
            let (clr, ((cb, cw, co, cg, cl), curr_cards), troph) = get_current_player player_list color in
            let new_inventory = match res with (* Add taken resources to current inventory *)
              | Brick -> ((cb + spoils), cw, co, cg, cl)
              | Wool -> (cb, (cw + spoils), co, cg, cl)
              | Ore -> (cb, cw, (co + spoils), cg, cl)
              | Grain -> (cb, cw, co, (cg + spoils), cl)
              | Lumber -> (cb, cw, co, cg, (cl + spoils))
            in let new_players = update_player_inventory ruined_players new_inventory color [] in (* Rebuild player list *)
            (None, (board, new_players, turn, (color, ActionRequest)))

        | EndTurn -> 
            match turn.dicerolled with
            | Some _ -> (* Dice rolled, end turn *)
              let new_turn = {  (* Update active player color *)
                active: (next_turn turn.active);
                dicerolled: turn.dicerolled;
                cardplayed: turn.cardplayed;
                cardsbought: turn.cardsbought;
                tradesmade: turn.tradesmade;
                pendingtrade: turn.pendingtrade;
              } in
              let new_state = (board, player_list, new_turn, ((next_turn color), ActionRequest)) in
              (None, new_state)
            (* If no dice has been rolled, substitute dice roll move because dice roll is required for turn *)
            | None -> handle_move_helper (board, player_list, turn, (color, ActionRequest)) (Action(RollDice))
      | _ -> handle_move (board, player_list, turn, (color, ActionRequest)) (Action(EndTurn)) (* Action end turn *)
  in handle_move_helper s m

let presentation s = failwith "Were not too much to pay for birth."
