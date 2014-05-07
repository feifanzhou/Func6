open Definition
open Registry
open Constant
open Util

(** Give your bot a 2-20 character name. *)
let name = "bot"

module Bot = functor (S : Soul) -> struct
  (* If you use side effects, start/reset your bot for a new game *)
  let initialize () = ()

  let rec boardtraverser portl =
    match portl with
     | ((p1,p2),ratio,portresource)::tl -> (match portresource with
      | PortResource(Brick) -> InitialMove(p1,p2)
      | _ -> boardtraverser tl)
     | [] -> InitialMove(0,0)
  
  let rec bt_helper board = match board with 
    | (map,_,_,_,_) -> (match map with
      | (hexl,portl) -> boardtraverser portl)
  
  let rec sufficient_resources player c = match player with
    | (color,hand,trophies)::t -> 
      if color = c then
        (match hand with
          (inventory,cards) -> 
            if num_resource_in_inventory inventory Brick > 1 && num_resource_in_inventory inventory Lumber > 1
            then true
            else false)
      else sufficient_resources t c 
    | _ -> failwith "player not found in list"

  let road_helper board color = match board with
    | (_,structures,_,_,_) -> (match structures with
      | (_,roads) -> 
        let rec road_list_traverser road_list = (match road_list with
        | (c,(p1,p2))::t -> 
          if c = color then let adj = adjacent_points p1 in 
          let rec helper adjacent = (match adjacent with
            | h::t -> 
              if (List.exists (fun (_,(a,b)) -> a != h || b != h) road_list) then (p1,h)
              else helper t
            | _ -> (p1,p2)) 
          in helper adj
          else road_list_traverser t
        | _ -> (0,1))
        in road_list_traverser roads) 

  let rec trade_helper player c = match player with
    | (color,hand,trophies)::t -> 
      if color = c then 
        (match hand with
          (inventory,cards) -> 
          if num_resource_in_inventory inventory Brick = 0 then
            (if num_resource_in_inventory inventory Wool > 1 then (true, (Brick, Wool))
            else if num_resource_in_inventory inventory Ore > 1 then (true, (Brick, Ore))
            else if num_resource_in_inventory inventory Grain > 1 then (true, (Brick, Grain))
            else (false, (Brick, Brick)))
          else if num_resource_in_inventory inventory Lumber = 0 then
            (if num_resource_in_inventory inventory Wool > 1 then (true, (Lumber, Wool))
            else if num_resource_in_inventory inventory Ore > 1 then (true, (Lumber, Ore))
            else if num_resource_in_inventory inventory Grain > 1 then (true, (Lumber, Grain))
            else (false, (Brick, Brick)))
          else (false, (Brick, Brick)))
      else trade_helper t c
    | _ -> (false, (Brick,Brick))

  (* Invalid moves are overridden in game *)
  let handle_request ((b,p,t,n) : state) : move =
    let (c, r) = n in
    match r with
      | InitialRequest -> bt_helper b
      | RobberRequest -> RobberMove(0, None)
      | DiscardRequest-> DiscardMove(0,0,0,0,0)
      | TradeRequest -> 
        if sufficient_resources p c then TradeResponse(false)
        else TradeResponse(true)
      | ActionRequest -> 
        if is_none t.dicerolled then Action(RollDice) 
        else if sufficient_resources p c then let (x,y) = road_helper b c in Action(BuyBuild(BuildRoad (c, (x,y))))
        else if fst (trade_helper p c) then let (x,y) = snd (trade_helper p c) in Action(MaritimeTrade(x,y))
        else Action(EndTurn) 
end


(* Do not change *)
let _ = register_bot name
  (module Bot(New)) (module Bot(New)) (module Bot(New)) (module Bot(New))
