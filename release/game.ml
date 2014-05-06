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
let rec get_player_inventory plist active_color = 
  let (clr, (inv, crds), troph) = get_current_player plist active_color in
  inv

let rec update_player_inventory plist new_inventory active_color acc = match plist with
  | (clr, hnd, troph)::t -> 
    if clr = active_color (* Is discarding player, update inventory in player list *)
    then update_player_inventory t ((clr, (new_inventory, curr_cards), troph)::acc)
    else update_player_inventory t ((clr, hnd, troph)::acc)  (* Just put same entry back in *)
  | [] -> List.rev acc (* Maintain player list order *)

let ports_with_settlements port_list settlement_list active_color = 
  let rec match_finder prtlst acc = match prtlst with
    | ((p1, p2), rtio, prtrsrc)::t -> 
      let itrx1 = List.nth settlement_list p1 in
      let itrx2 = List.nth settlement_list p2 in
      (* Check that intersection exists for either p1 or p2, and that the color matches the active color *)
      if ((itrx1 <> None) && ((fst itrx1) = active_color)) || ((itrx2 <> None) && ((fst itrx2) = active_color)
      then match_finder t (((p1, p2), rtio, prtrsrc)::acc)
      else match_finder t acc
    | [] -> List.rev acc (* Maintain order *)
  in match_finder port_list []

let pieces_for_roll roll = match roll with
  | 2 -> [17]
  | 3 -> [8, 15]
  | 4 -> [3, 10]
  | 5 -> [5, 16]
  | 6 -> [4, 18]
  | 8 -> [11, 12]
  | 9 -> [2, 14]
  | 10 -> [6, 13]
  | 11 -> [0, 9]
  | 12 -> [1]
  | _ -> []

let new_resources_for_settlements piece_list intersections_list active_color robber_pos = (* Need count of towns and cities for active player *)
  let rec helper pc_list (resources : cost) = match pc_list with (* For every piece, get its corners *)
    | h::t -> let piece_pos = snd h in
      if robber_pos = piece_pos then helper t total_town_count total_city_count else (* Skip robber piece *)
      let corners = piece_corners piece_pos in
      let rec corner_helper corner_list town_count city_count = match corner_list with
        | h'::t' -> let itrsc = List.nth intersections_list h' in (* Get settlement at every corner *)
          match itrsc with
          | None -> corner_helper t' town_count city_count (* If no settlement, check next corner *)
          | Some (clr, stlmt) -> (* If there is a settlement *)
            if clr = active_color (* Check its color *)
            then match stlmt with
              | City -> corner_helper t' town_count (city_count + 1)
              | Town -> corner_helper t' (town_count + 1) city_count
            else corner_helper t' town_count city_count (* Not active player's settlement *)
        | [] -> (* Move to next piece *)
          (* Calculate resource type and amount to add *)
          let resource_bump = town_count * (settlement_num_resources Town) + city_count * (settlement_num_resources Count) in
          let rsrc = resource_of_terrain (fst h) in
          match rsrc with
          | None -> helper t resources (* Pieie has no resources *)
          | Some (r) -> let (rb, rw, ro, rg, rl) = resources in (* Add resources *)
            match r with
            | Brick -> helper t ((rb + resource_bump), rw, ro, rg, rl)
            | Wool -> helper t (rb, (rw + resource_bump), ro, rg, rl)
            | Ore -> helper t (rb, rw, (ro + resource_bump), rg, rl)
            | Grain -> helper t (rb, rw, ro, (rg + resource_bump), rl)
            | Lumber -> helper t (rb, rw, ro, rg, (rl + resource_bump))
    | [] -> resources
  in helper piece_list (0, 0, 0, 0, 0)

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
        let new_turn = {
          active: turn.active;
          dicerolled: turn.dicerolled;
          cardplayed: turn.cardplayed;
          cardsbought: turn.cardsbought;
          tradesmade: turn.tradesmade;
          pendingtrade: None
        } in
        if not b then <> (* Trade rejected, try another move *)
          (None, (board, player_list, new_turn, (turn.active, ActionRequest)))
        else (* Conduct trade *) let (clr, c1, c2) = turn.pendingtrade in
          (* Current player's resources checked in DomesticTrade action handler below *)
          let (cb1, cw1, co1, cg1, cl1) = c1 in
          let (cb2, cw2, co2, cg2, cl2) = c2 in
          let (tcb, tcw, tco, tcg, tcl) = get_player_inventory player_list clr in 
          (* Check if target player has enough resources to satisfy trade *)
          if (tcb < cb2) || (tcw < cw2) || (tco < co2) || (tcg < cg2) || (tcl < cl2)
          then (None, (board, player_list, new_turn, (turn.active, ActionRequest)))
          else (* update inventories, save, outcome *)
            let new_p2_inventory = ((tcb - cb2 + cb1), (tcw - cw2 + cw1), (tco - co2 + co1), (tcg - cg2 + cg1), (tcl - cl2 + cl1)) in
            let (ccb, ccw, cco, ccg, ccl) = get_player_inventory player_list color in
            let new_p1_inventory = ((ccb - cb1 + cb2), (ccw - cw1 + cw2), (cco - co1 + co2), (ccg - cg1 + cg2), (ccl - cl1 + cl2)) in
            let new_player_list = update_player_inventory player_list new_p2_inventory clr [] in
            let new_player_list' = update_player_inventory new_player_list new_p1_inventory color [] in
            let new_turn_with_trade_count = {
              active: turn.active;
              dicerolled: turn.dicerolled;
              cardplayed: turn.cardplayed;
              cardsbought: turn.cardsbought;
              tradesmade: (turn.tradesmade + 1);
              pendingtrade: None
            }
            (None, (board, new_player_list', new_turn_with_trade_count, (turn.active, ActionRequest)))
    | ActionRequest -> 
      match m' with
      | Action a ->
        match a with (* TODO: Sub rolldice move if turn.dicerolled = None *)
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
          else (* Didn't roll robber, generate resources *)
            let activated_pieces = pieces_for_roll roll_num in
            let (mp, str, dk, dscrd, rbr) = board in
            let itrsc_list = fst (snd board) in
            let rec players_helper plist acc = match plist with (* Build new player list with resources *)
              | (clr, (inv, crds), troph)::t -> let new_inv = new_resources_for_settlements activated_pieces itrsc_list clr rbr in
                let new_player = (clr, (new_inv, crds), troph) in
                players_helper t (new_player::acc)
              | [] -> List.rev acc
            in let new_player_list = players_helper player_list [] in
            (None, (board, new_player_list, rolled_turn, (color, ActionRequest)))
        | MaritimeTrade (resource1, resource2) -> 
          (* Get list of ports with settlements
             If list is blank, then trade at 4:1 ratio
             If those ports have the supported resource, trade at 2:1 ratio
             Else trade at 3:1 ratio *)
          let itrscs = fst (snd board) in
          let ports = snd (fst board) in
          let settled_ports = ports_with_settlements ports itrscs color in
          let trade_ratio = if List.length settled_ports = 0 then 4 else
            let rec find_resourceful_port_ratio prtlst = match prtlst with
              | (ln, rtio, prtrsrc)::t -> match prtrsrc with
                | PortResource(rsrc) -> if rsrc = resource1 then rtio else find_resourceful_port t
                | Any -> find_resourceful_port t
              | [] -> 3 (* No resourceful port found *)
            in find_resourceful_port_ratio settled_ports in
          let (cb, cw, co, cg, cl) = get_player_inventory player_list color in
          let reduced_inventory = match resource1 with (* Remove r1 from inventory if possible *)
            | Brick -> if cb < trade_ratio then None else Some ((cb - trade_ratio), cw, co, cg, cl)
            | Wool -> if cw < trade_ratio then None else Some (cb, (cw - trade_ratio), co, cg, cl)
            | Ore -> if co < trade_ratio then None else Some (cb, cw, (co - trade_ratio), cg, cl)
            | Grain -> if cg < trade_ratio then None else Some (cb, cw, co, (cg - trade_ratio), cl)
            | Lumber -> if cl < trade_ratio then None else Some (cb, cw, co, cg, (cl - trade_ratio))
          in match reduced_inventory with (* Perform trade, or exit if not enough r1 *)
            | None -> (None, (board, player_list, turn, (color, ActionRequest)))
            | Some (rb, rw, ro, rg, rl) -> let new_inventory = match resource2 with
                | Brick -> ((rb + 1), rw, ro, rg, rl)
                | Wool -> (rb, (rw + 1), ro, rg, rl)
                | Ore -> (rb, rw, (ro + 1), rg, rl)
                | Grain -> (rb, rw, ro, (rg + 1), rl)
                | Lumber -> (rb, rw, ro, rg, (rl + 1))
              in let new_player_list = update_player_inventory player_list new_inventory color [] in
              (None, (board, new_player_list, turn, (color, ActionRequest)))
        | DomesticTrade (target_color, cost1, cost2) -> (* Need to check if max trades exceeded or if player has enough inventory *)
          let bail_move = (None, (board, player_list, turn, (color, ActionRequest))) in
          if turn.tradesmade > cNUM_TRADES_PER_TURN then bail_move
          else (* Check current player inventory *)
            let (cb, cw, co, cg, cl) = get_player_inventory player_list color in 
            let (cb1, cw1, co1, cg1, cl1) = cost1 in
            if (cb < cb1) || (cw < cw1) || (co < co1) || (cg < cg1) || (cl < cl1) then bail_move
            else let new_turn = {
              active: turn.active;
              dicerolled: turn.dicerolled;
              cardplayed: turn.cardplayed;
              cardsbought: turn.cardsbought;
              tradesmade: turn.tradesmade;
              pendingtrade: Some (target_color, cost1, cost2);
            } in
            (None, (board, player_list, new_turn, (target_color, TradeRequest)))
        | BuyBuild b -> failwith "Not yet"
        | PlayCard pc -> if turn.cardplayed then (None, (board, player_list, turn, (color, ActionRequest))) else (* Only one dev card per turn *)
          let new_turn = {
            active: turn.active;
            dicerolled: turn.dicerolled;
            cardplayed: true;
            cardsbought: turn.cardsbought;
            tradesmade: turn.tradesmade;
            pendingtrade: turn.pendingtrade;
          } in
          match pc with (* TODO: Something about knights and army size? *)
          | PlayKnight (rbrmv) -> handle_move_helper (board, player_list, new_turn, (color, RobberRequest)) (RobberMove(rbrmv))
          | PlayRoadBuilding (rd, rdopt) ->
            let (mp, (intrs, rds), dk, dsc, rbr) = board in
            let roads_to_add = match rdopt with
              | None -> [rd]
              | Some (other_road) -> [rd, other_road]
            in let new_roads = List.append rds roads_to_add in
            (None, (board, player_list, new_turn, (color, ActionRequest)))
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
            (None, (board, new_player_list, new_turn, (color, ActionRequest)))
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
            (None, (board, new_players, new_turn, (color, ActionRequest)))
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
      | _ -> let next_action = (if turn.dicerolled = None then Action(RollDice) else Action(EndTurn)) in
             handle_move (board, player_list, turn, (color, ActionRequest)) (next_action)
  in handle_move_helper s m

let presentation s = failwith "Were not too much to pay for birth."
