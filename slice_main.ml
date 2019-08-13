open Asttypes
open Parsetree
open Debug_core

let rec find_exp f exp = match exp with
  | {pexp_desc = desc; pexp_loc = _; pexp_attributes = _} ->
     (match desc with
      | Pexp_ident(_) | Pexp_constant(_) | Pexp_construct(_, None)
      | Pexp_assert(_) ->
         f exp
      | Pexp_let(_, vbs, e) ->
         (List.concat (List.map (fun {pvb_expr = e} -> (find_exp f e)) vbs))
         @ (find_exp f e)
      | Pexp_function(cases) ->
         (List.concat (List.map (fun {pc_rhs = e} -> (find_exp f e)) cases))
      | Pexp_fun(_, None, _, e) ->
         find_exp f e
      | Pexp_fun(_, Some(e1), _, e2) ->
         (find_exp f e1) @ (find_exp f e2)
      | Pexp_apply(o_e, o_aes) ->
         (find_exp f o_e) @ (List.concat (List.map (fun (_, o_e) -> find_exp f o_e) o_aes))
      | Pexp_match(e,cases) | Pexp_try(e,cases) ->
         (find_exp f e) @ (List.concat (List.map (fun {pc_rhs = e} -> (find_exp f e)) cases))
      | Pexp_tuple(es) ->
         List.concat (List.map (fun e -> find_exp f e) es)
      | Pexp_construct(_, Some(e)) ->
         find_exp f e
      | Pexp_ifthenelse(e1, e2, None) ->
         (find_exp f e1) @ (find_exp f e2)
      | Pexp_ifthenelse(e1, e2, Some(e3)) ->
         (find_exp f e1) @ (find_exp f e2) @ (find_exp f e3)
      | Pexp_record(les, None) ->
         (List.concat (List.map (fun (_, o_e) -> find_exp f o_e) les))
      | Pexp_record(les, Some(e)) ->
         (List.concat (List.map (fun (_, o_e) -> find_exp f o_e) les)) @ (find_exp f e)
      | Pexp_sequence(e1, e2) ->
         (find_exp f e1) @ (find_exp f e2)
      | Pexp_constraint(e, _) ->
         (find_exp f e)
      | _ ->
         Format.fprintf ppf "@[Syntax Error: Sorry. This program includes not-supported syntax.: %a@]@." Pprintast.expression exp;
         assert false)
    
let locs_slice_s slice = 
  find_exp (fun {pexp_desc = _; pexp_loc = l; pexp_attributes = att} ->
      if (List.exists (fun ({txt = name}, _) -> name = "exp") att)
      then []
      else [l]) slice
     
let rec locs_slice_e slice = match slice with
  | [] -> []
  | {pstr_desc = Pstr_type(_)} :: rest -> locs_slice_e rest
  | {pstr_desc = Pstr_eval(o_e, _)} :: rest -> (locs_slice_s o_e) @ (locs_slice_e rest)
  | {pstr_desc = Pstr_value(_, vbs1)} :: rest ->
     let ls = List.concat (List.map (fun {pvb_pat = _; pvb_expr = m; pvb_attributes = _; pvb_loc = _} -> locs_slice_s m) vbs1) in
     ls @ (locs_slice_e rest)
  | {pstr_desc = _} :: rest -> locs_slice_e rest

(* 条件によっては 終了、そうでなければ map *)
let rec map_exps cond f exp = 
    if cond exp then f exp
    else
      (match exp with
       | {pexp_desc = desc; pexp_loc = l; pexp_attributes = att} ->
          (fun exp -> {pexp_desc = exp; pexp_loc = l; pexp_attributes = att})
          (match desc with
             Pexp_ident(_) | Pexp_constant(_) | Pexp_construct(_, None) | Pexp_assert (_) ->
                              desc
             | Pexp_let(r, vbs, e) ->
                Pexp_let(r, List.map (fun {pvb_pat = p; pvb_expr = e; pvb_attributes = att; pvb_loc = l} -> {pvb_pat = p; pvb_expr =  map_exps cond f e; pvb_attributes = att; pvb_loc = l}) vbs, map_exps cond f e)
             | Pexp_function(cases) ->
                Pexp_function(List.map (fun {pc_lhs = p; pc_guard = eop; pc_rhs = e} -> {pc_lhs = p; pc_guard = eop; pc_rhs = map_exps cond f e}) cases)
             | Pexp_fun(a, None, p, e) ->
                Pexp_fun(a, None, p, map_exps cond f e)
             | Pexp_fun(a, Some(e1), p, e) ->
                Pexp_fun(a, Some(map_exps cond f e1), p, map_exps cond f e)
             | Pexp_apply(o_e, o_aes) ->
                Pexp_apply(map_exps cond f o_e, List.map (fun (a, k) -> (a, map_exps cond f k)) o_aes)
             | Pexp_match(e,cases) ->
                Pexp_match(map_exps cond f e, List.map (fun {pc_lhs = p; pc_guard = eop; pc_rhs = e} -> {pc_lhs = p; pc_guard = eop; pc_rhs = map_exps cond f e}) cases)
             | Pexp_try(e,cases) ->
                Pexp_try(map_exps cond f e, List.map (fun {pc_lhs = p; pc_guard = eop; pc_rhs = e} -> {pc_lhs = p; pc_guard = eop; pc_rhs = map_exps cond f e}) cases)
             | Pexp_tuple(es) ->
                Pexp_tuple(List.map (fun e -> map_exps cond f e) es)
             | Pexp_construct(l, Some(e)) ->
                Pexp_construct(l, Some(map_exps cond f e))
             | Pexp_ifthenelse(e1, e2, None) ->
                Pexp_ifthenelse(map_exps cond f e1, map_exps cond f e2, None)
             | Pexp_ifthenelse(e1, e2, Some(e3)) ->
                Pexp_ifthenelse(map_exps cond f e1, map_exps cond f e2, Some(map_exps cond f e3))
             | Pexp_record(les, None) ->
                Pexp_record(List.map (fun (l, e) -> (l, map_exps cond f e)) les, None)
             | Pexp_record(les, Some(e)) ->
                Pexp_record(List.map (fun (l, e) -> (l, map_exps cond f e)) les, Some(map_exps cond f e))
             | Pexp_sequence(e1, e2) ->
                Pexp_sequence(map_exps cond f e1, map_exps cond f e2)
             | Pexp_constraint(e, t) ->
                Pexp_constraint(map_exps cond f e, t)
             | _ -> Format.fprintf ppf "@[Syntax Error: Sorry. This program includes not-supported syntax.: %a@]@." Pprintast.expression exp;
                    assert false))

let pierce_exp loc slice =
    map_exps (fun {pexp_desc = _; pexp_loc = l; pexp_attributes = att} ->
        if loc = l && (not (List.exists (fun ({txt = name}, _) -> name = "exp") att)) then true else false) (fun exp -> hole_of_exp exp) slice

let rec pierce_str loc slice = match slice with
  | [] -> []
  | {pstr_desc = str; pstr_loc = l1} :: rest ->
     (match str with
      | Pstr_eval(e, m) ->
         ((fun str -> {pstr_desc = str; pstr_loc = l1})
            (Pstr_eval ((pierce_exp loc e), m))) :: (pierce_str loc rest)
      | Pstr_value(k, vbs) ->
         ((fun str -> {pstr_desc = str; pstr_loc = l1})
            (Pstr_value(k, List.map (fun {pvb_pat = p; pvb_expr = m; pvb_attributes = a; pvb_loc = l} -> {pvb_pat = p; pvb_expr = (pierce_exp loc m); pvb_attributes = a; pvb_loc = l}) vbs))) :: (pierce_str loc rest)
      | _ ->  {pstr_desc = str; pstr_loc = l1} :: (pierce_str loc rest))
    
let rec add loc lst = match lst with
  | [] -> [(loc, 1)]
  | (fst, n) :: rest -> if loc = fst then (fst, n + 1) :: rest
                        else (fst, n) :: (add loc rest)

let rec overlay_slice slices lst = match slices with
  | [] -> lst
  | (locs, _) :: rest ->
     let rec loop locs acc = match locs with
       | [] -> acc
       | fst :: rest ->
          loop rest (add fst acc)
     in overlay_slice rest (loop locs lst)

let sort_list lst =
  List.sort (fun (_, m) (_, n) -> if m > n then -1 else if m = n then 0 else 1) lst

let overlay_slice slices lst =
  sort_list (overlay_slice slices lst)

let rec remove_non locs = match locs with
  | [] -> []
  | f :: rest -> if f = Location.none then (remove_non rest)
                 else f :: (remove_non rest)                        

let rec in_quest lst n = match lst with
  | [] -> false
  | fst :: rest -> if fst = n then true
                   else in_quest rest n

let rec msdb_loop strs initial_env ppf slices =
  (* let k = Sys.time () in *)
  let slice' = Debug_slice.get_slice_top (Debug_core.hole_str :: strs) (initial_env ()) in
  (* Format.fprintf ppf "Slicing time! %f\n\n" (Sys.time () -. k); *)

  let locs = remove_non (locs_slice_e slice') in
  let slices = ((locs, slice') :: slices) in

  let rec loop slices strs complete_set = match slices with
    | [] -> (strs, complete_set)
    | _ -> 
       let contribute_locs = overlay_slice slices [] in
       (match contribute_locs with
        | [] -> (Format.fprintf ppf "Error: Sorry. This program includes errors caused by only nodes. Our system targets fix of leaves.\n"; exit 0)
        | _ -> ());
       let (l, _) = List.hd contribute_locs in
       let strs' = pierce_str l strs in
       loop (List.filter (fun (s, _) -> not (in_quest s l)) slices) strs' (l::complete_set )in
  let (strs', complete_set) = loop slices strs [] in
  (try(
     let _ = Typemod.type_structure (initial_env ()) ( Debug_core.hole_str ::  strs') Location.none in
     (slices, complete_set)
   ) with
     ((Typecore.Error(_, _, Typecore.Expr_type_clash(_))) |
	    (Typecore.Error(_, _, Typecore.Pattern_type_clash(_))) |
	  (Typecore.Error(_, _, Typecore.Apply_non_function(_))) |
	  (Typecore.Error(_, _, Typecore.Wrong_name(_)))) | _ ->
  msdb_loop strs' initial_env ppf slices)
  
let rec remove_dup lst1 lst2 = match lst1 with
  | [] -> []
  | fst :: rest ->
     try(ignore(List.find (fun x -> x = fst) lst2); remove_dup rest lst2)
     with Not_found -> fst :: (remove_dup rest lst2)

let rec remove_str locs str = match locs with
  | [] -> str
  | fst :: rest -> remove_str rest (pierce_str fst str)

let rec cs_loop cs b set = match cs with
  | [] -> (b, set)
  | l :: rest ->
     Location.print ppf l;
     Format.fprintf ppf "In a complete set: This might be source of type error.\n Is this the error source? (y/n)\n>";
     let st = read_line () in
     if st = "y;;" || st = "y" then
       (Format.fprintf ppf "Located!\n"; cs_loop rest b (l::set))
     else if st = "q;;" || st = "q" then
       exit 0
     else 
       cs_loop rest false set
     
let rec check strs ls initial_env = match ls with
  | [] -> (try(
             let _ = Typemod.type_structure (initial_env ()) ( Debug_core.hole_str ::  strs) Location.none in
             true
           ) with ((Typecore.Error(_, _, Typecore.Expr_type_clash(_))) |
	             (Typecore.Error(_, _, Typecore.Pattern_type_clash(_))) |
	           (Typecore.Error(_, _, Typecore.Apply_non_function(_))) |
	           (Typecore.Error(_, _, Typecore.Wrong_name(_)))) -> false)
  | l :: rest -> 
     let e = pierce_str l strs in
     check e rest initial_env
     
let launch_msdb strs initial_env ppf =
  (* let a = Sys.time () in *)
  let (slices, complete_set)  = msdb_loop strs initial_env ppf [] in
  let contribute_locs =  overlay_slice slices [] in
  (* Format.fprintf ppf "@[~total time %f~@]@." (Sys.time () -. a); *)

  let locs = remove_dup (locs_slice_e strs) (List.concat (List.map fst slices)) in
  let strs = remove_str locs strs in
  
  (* asking correcting set *)
  let (b, set) = cs_loop complete_set true [] in

  let rec ranking_loop lst set' = match lst with
  | [] -> (Format.fprintf ppf "Sorry. There is no more candidates.\n"; exit 0)
  | (l, n) :: rest ->
     let is = List.filter (fun x -> x = l) complete_set in
     (match is with
      | [] ->
         (Location.print ppf l;
          Format.fprintf ppf "%d slice(s) say this might be source of type error.\n Is this the error source? (y/n)\n>" n;
          let st = read_line () in
          if st = "y;;" || st = "y" then
            (if check strs (l::set') initial_env then
               Format.fprintf ppf "All error source(s) located!"
             else ranking_loop rest (l::set'))
          else ranking_loop rest set')
      | _ -> ranking_loop rest set) in
  (* asking ranking set *)
  if b then ()
  else ranking_loop contribute_locs set
