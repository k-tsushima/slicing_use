(* This file is written by Naho Wakikawa and Kanae Tsushima. *)

(* open Misc *)
(* open Path *)
open Asttypes
open Ast_helper

(* open Types *)
open Typedtree
(* open Ctype *)
(* open Format *)

open Parsetree

open Debug_core


type expr_cxt = expression -> expression
type item_cxt = expr_cxt -> expression -> structure
type structure_cxt = (structure_item * Env.t) list -> structure -> structure

(* go *)
(* 'a context_t を引数に持つ関数を、最後に 'a 型で受け取る形にする。 *)
(* かっこを減らせる, 'a 型の引数で再帰する関数に渡すときに便利。 *)
let go f prefix env cxt x = f ((x, cxt), env, prefix)


(* id : 'a -> 'a *)
let id = fun x -> x

(*

(* map2_... : (expression -> pattern -> expression) -> (expression -> pattern -> pattern) -> 'a -> 'a *)
(* 引数中に含まれる expression と pattern を書き換えるために使う *)
let map2_vb fun_exp fun_pat {pvb_pat = p; pvb_expr = e; pvb_attributes = a; pvb_loc = l} =
  {pvb_pat = fun_pat p e; pvb_expr = fun_exp p e; pvb_attributes = a; pvb_loc = l}
and map2_case fun_exp fun_pat {pc_lhs = p; pc_guard = g; pc_rhs = e} =
  {pc_lhs = fun_pat p e; pc_guard = g; pc_rhs = fun_exp p e}
and map2_le fun_exp _ (l, e) = (l, fun_exp wildcard e)
(*
and map2_lp _ fun_pat (l, p) = (l, fun_pat p skeleton')
 *)
(* map_... : (expression -> expression) -> (pattern -> pattern) -> 'a -> 'a *)
(* 1引数関数バージョン *)
let map_vb fun_exp fun_pat vb =
  let fun_exp' = fun _ e -> fun_exp e in
  let fun_pat' = fun p _ -> fun_pat p in
  map2_vb fun_exp' fun_pat' vb
and map_case fun_exp fun_pat case =
  let fun_exp' = fun _ e -> fun_exp e in
  let fun_pat' = fun p _ -> fun_pat p in
  map2_case fun_exp' fun_pat' case
and map_le fun_exp fun_pat le =
  let fun_exp' = fun _ e -> fun_exp e in
  let fun_pat' = fun p _ -> fun_pat p in
  map2_le fun_exp' fun_pat' le
 *)
(*
and map_lp fun_exp fun_pat lp =
  let fun_exp' = fun _ e -> fun_exp e in
  let fun_pat' = fun p _ -> fun_pat p in
  map2_lp fun_exp' fun_pat' lp
 *)
(********** pattern slicing **********)
let rec pattern_variables pat = match pat.ppat_desc with
    Ppat_any -> []
  | Ppat_var ({txt = st}) -> [st]
  | Ppat_alias (p, {txt = st}) -> st :: pattern_variables p
  | Ppat_constant (_) -> []
  | Ppat_interval (_, _) -> []
  | Ppat_tuple (ps) -> List.flatten (List.map pattern_variables ps)
  | Ppat_construct (_, None) -> []
  | Ppat_construct (_, Some (p)) -> pattern_variables p
  | Ppat_variant (_, None) -> []
  | Ppat_variant (_, Some (p)) -> pattern_variables p
  | Ppat_record (lps, _) ->
      List.flatten (List.map (fun (_, p) -> pattern_variables p) lps)
  | Ppat_array (ps) -> List.flatten (List.map pattern_variables ps)
  | Ppat_or (p1, p2) -> pattern_variables p1 @ pattern_variables p2
  | Ppat_constraint (p, _) -> pattern_variables p
  | Ppat_type (_) -> []
  | Ppat_lazy (p) -> pattern_variables p
  | Ppat_unpack ({txt = st}) -> [st]
  | Ppat_exception (p) -> pattern_variables p
  | Ppat_extension (_) -> []
  | Ppat_open (_, p) -> pattern_variables p
(********** expr_context **********)
(*
type expr_context =
  | Empty
  | Lambda of pattern * expr_context
    (* TODO: incorporate labeled arguments, currently ignored *)
  | Let of rec_flag * value_binding list * expr_context
let print_cxt cxt = match cxt with
  | Empty -> "Empty"
  | Lambda(_) -> "Lambda"
  | Let(_) -> "Let"
 *)
(********** plug **********)
(*
(* plug_expr : expression -> expr_context -> expression *)
let rec plug_expr expr cxt = match cxt with
  | Empty -> expr
  | Lambda (pat, c) ->
      (* パターン変数を全て集め *)
      let vars = pattern_variables pat in
      (* 変数名から変数の expression を作る *)
      let varexp x = Exp.mk (Pexp_ident (mknoloc (Longident.Lident x))) in
      (* expr と組にして body に入れる。これでパターン変数の型を知る *)
      (* ダミーの 0 を入れるのは、tuple 長が 2 以上でないとエラーになるため *)
      let body = Exp.mk (Pexp_tuple
                          (expr :: dummy_int0 :: List.map varexp vars)) in
      let exp = Exp.mk (Pexp_fun (Nolabel, None, pat, body)) in
      plug_expr exp c
  | Let (flag, bindings, c) ->
      plug_expr { pexp_desc        = Pexp_let (flag, bindings, expr);
                  pexp_loc         = Location.none;
                  pexp_attributes  = [] }
                c

(* plug_str : (expression * expr_context) -> structure *)
let plug_str (expr, cxt) =
  [{ pstr_desc = Pstr_eval (plug_expr expr cxt, []);
     pstr_loc  = Location.none }]
 *)
(********** pattern **********)
(*
(* desc_to_desc : pattern_desc -> expression_desc option *)
let rec desc_to_desc pat = match pat with
  | Ppat_any ->
     (* _ *)
     None
  | Ppat_var({txt = st; loc = loc'}) ->
     (* Ppat_var of string loc *)
     (* x *)
     Some (Pexp_ident({txt = Longident.Lident(st); loc = loc'}))
  | Ppat_tuple(ps) ->
     (* Ppat_tuple of pattern list *)
     (* (P1, ..., Pn)
           Invariant: n >= 2
      *)
     Some (Pexp_tuple(List.map pat_to_exp ps))
  | Ppat_constant (c) ->
     (* 1, 'a', "true", 1.0, 1l, 1L, 1n *)
     Some (Pexp_constant (c))
  | Ppat_construct (lid, p) ->
     (* Ppat_construct of Longident.t loc * pattern option *)
     (* C                None
           C P              Some P
           C (P1, ..., Pn)  Some (Ppat_tuple [P1; ...; Pn])
      *)
     Some (Pexp_construct (lid, match p with None -> None | Some p' -> Some (pat_to_exp p')))
  | Ppat_record (lps, (*flg*)_) ->
  (* Ppat_record of (Longident.t loc * pattern) list * closed_flag *)
  (* { l1=P1; ...; ln=Pn }     (flag = Closed)
           { l1=P1; ...; ln=Pn; _}   (flag = Open)

           Invariant: n > 0
   *)


     Some (Pexp_record (List.map (fun (l, p) -> (l, pat_to_exp p)) lps, None))
  | Ppat_constraint (p, ct) ->
     Some (Pexp_constraint (pat_to_exp p, ct))
  | _ -> None

(* pat_to_exp : pattern -> expression option *)
and pat_to_exp {ppat_desc = d; ppat_loc = l; ppat_attributes = a} =
  match desc_to_desc d with
  | None -> skeleton
  | Some (d') -> {pexp_desc = d'; pexp_loc = l; pexp_attributes = a}
 *)

let unconstraint_pat pat cxt = match pattern_variables pat with
  | [] -> cxt
  | first :: [] ->
     Lambda (
         desc_to_pat (
             Ppat_var ({txt = first; loc = Location.none})
           ) pat, cxt)
  | lst ->
     Lambda (
         desc_to_pat (
             Ppat_tuple (
                 List.map (
                     fun s -> desc_to_pat (
                                  Ppat_var ({txt = s; loc = Location.none})
                                ) pat
                   ) lst)
           ) pat, cxt)

let rec plug_cxt cxt1 cxt2 = match cxt1 with
  | Empty -> cxt2
  | Lambda (pat, cxt') -> Lambda(pat, plug_cxt cxt' cxt2)
  | Let (st, t, cxt') -> Let(st, t, plug_cxt cxt' cxt2)

(********** obtain type and environment of expr **********)

(* type of elements of yes/no list *)
(* type yes_no_list = (string context_t * type_expr) list *)
(* yes_no_list という名前を使っているが、ここでは環境として使っている *)

(* collect_one : (string context_t * type_expr) context_t -> string list ->
                 type_expr -> yes_no_list * type_expr *)
let collect_one ((vartyps, cxt'), env, prefix) vars typ =
  match decode_tuple typ with
      Some (exp_typ :: _ :: typs) -> (* _ は dummy_int0 の型 *)
        (List.map2 (fun v t -> (((v, cxt'), env, prefix), t)) vars typs
         @ vartyps,
         exp_typ)
    | Some ([_]) | Some ([]) | None ->
        Format.fprintf ppf "type:@.%a@." Printtyp.type_expr typ;
        failwith "TypeDebugger: Error in collect_one"
  (*
  match typ.desc with
      Tlink (typ') -> collect_one ((vartyps, cxt'), env, prefix) vars typ'
    | Ttuple (exp_typ :: typs) ->
        (List.map2 (fun v t -> (((v, cxt'), env, prefix), t)) vars typs
         @ vartyps,
         exp_typ)
    | _ ->
        Format.fprintf ppf "type:@.%a@." Printtyp.type_expr typ;
        failwith "TypeDebugger: Error in collect_one"
  *)
(*
let rec collect_one ((vartyps, cxt'), env, prefix) p t = match t.desc with
    Tarrow (_, t1, t2, _) ->
      (obtain_pattern_types ((p, cxt'), env, prefix) t1 @ vartyps, t2)
      (*
      begin match p with
          { ppat_desc = Ppat_var ({txt = st}) } ->
            ((((st, cxt'), env, prefix), t1) :: vartyps, t2)
        | _ -> (vartyps, t2) (* パターンが変数以外だったら無視されてる *)
      end
      *)
  | Tlink (t') -> collect_one ((vartyps, cxt'), env, prefix) p t'
  | _ -> failwith "TypeDebugger: Error in collect_one"
*)

(* collect : expression context_t -> type_expr -> yes_no_list * type_expr *)
let rec collect ((expr, cxt), env, prefix) t = match cxt with
    Empty -> ([], t)
  | Lambda (pat, cxt') ->
      (* There and back again [Danvy&Goldberg ICFP'02] *)
      let (vartyps, t') = collect ((expr, cxt'), env, prefix) t in
      let vars = pattern_variables pat in
      begin match split_arrow t' with
          Some ((*t1*)_, t2) ->
            collect_one ((vartyps, cxt'), env, prefix) vars t2
        | None -> (* Can't happen *)
            failwith "TypeDebugger: Error in collect"
      end
  | Let (_, _, cxt') -> collect ((expr, cxt'), env, prefix) t

(*
let rec replace_pat st pat = match pat.ppat_desc with
  | Ppat_any -> pat
  | Ppat_var ({txt = st'}) ->
     if st = st' then desc_to_pat Ppat_any pat else pat
  | Ppat_alias (p, {txt = st'; loc = loc'}) ->
     desc_to_pat (if st = st' then Ppat_any
                  else (Ppat_alias (replace_pat st p, {txt = st';
                                                       loc = loc'}))) pat
  | Ppat_constant (_) -> dummy_pattern pat
  | Ppat_interval (_, _) -> pat
  | Ppat_tuple (ps) ->
     desc_to_pat (Ppat_tuple (List.map (replace_pat st) ps)) pat
  | Ppat_construct (lid, None) -> pat
  | Ppat_construct (lid, Some (p)) ->
     desc_to_pat (Ppat_construct (lid, Some (replace_pat st p))) pat
  | Ppat_variant (_, None) -> pat
  | Ppat_variant (l, Some (p)) ->
     desc_to_pat (Ppat_variant (l, Some (replace_pat st p))) pat
  | Ppat_record (lps, flg) ->
     desc_to_pat (Ppat_record (List.map (fun (l, p) -> (l, replace_pat st p)) lps, flg)) pat
  | Ppat_array (ps) ->
     desc_to_pat (Ppat_array (List.map (replace_pat st) ps)) pat
  | Ppat_or (p1, p2) ->
     desc_to_pat (Ppat_or (replace_pat st p1, replace_pat st p2)) pat
  | Ppat_constraint (p, ct) ->
     desc_to_pat (Ppat_constraint (replace_pat st p, ct)) pat
  | Ppat_type (_) -> pat
  | Ppat_lazy (p) ->
     desc_to_pat (Ppat_lazy (replace_pat st p)) pat
  | Ppat_unpack ({txt = st'}) ->
     if st = st' then desc_to_pat Ppat_any pat else pat
  | Ppat_exception (p) ->
     desc_to_pat (Ppat_exception (replace_pat st p)) pat
  | Ppat_extension (_) -> pat
  | Ppat_open (_, p) -> pat
 *)
let rec replace_pat st pat = match pat.ppat_desc with
  | Ppat_any -> pat
  | Ppat_var ({txt = st'}) ->
     if st = st' then hole_of_pat pat else pat
  | Ppat_alias (p, {txt = st'; loc = loc'}) ->
     desc_to_pat (* if st = st' then pat.ppat_desc *) (* TODO:消していいかはチェックが必要。現状では全て残しておく *)
                  (Ppat_alias (replace_pat st p, {txt = st';
                                                       loc = loc'})) pat
  | Ppat_constant _ -> dummy_any pat
  | Ppat_interval _ -> pat
  | Ppat_tuple (ps) ->     
     desc_to_pat (Ppat_tuple (List.map (replace_pat st) ps)) pat
  | Ppat_construct (_, None) -> pat
  | Ppat_construct (lid, Some (p)) ->
     desc_to_pat (Ppat_construct (lid, Some (replace_pat st p))) pat
  | Ppat_variant (_, None) -> pat
  | Ppat_variant (l, Some (p)) ->
     desc_to_pat (Ppat_variant (l, Some (replace_pat st p))) pat
  | Ppat_record (lps, flg) ->
     desc_to_pat (Ppat_record (List.map (fun (l, p) -> (l, replace_pat st p)) lps, flg)) pat
  | Ppat_array (ps) ->
     desc_to_pat (Ppat_array (List.map (replace_pat st) ps)) pat
  | Ppat_or (p1, p2) ->
     desc_to_pat (Ppat_or (replace_pat st p1, replace_pat st p2)) pat
  | Ppat_constraint (p, ct) ->
     desc_to_pat (Ppat_constraint (replace_pat st p, ct)) pat
  | Ppat_type _ -> pat
  | Ppat_lazy (p) ->
     desc_to_pat (Ppat_lazy (replace_pat st p)) pat
  | Ppat_unpack ({txt = st'}) ->
     if st = st' then hole_of_pat pat else pat
  | Ppat_exception (p) ->
     desc_to_pat (Ppat_exception (replace_pat st p)) pat
  | Ppat_extension _ -> pat
  | Ppat_open _ -> pat

exception Pat_slice_error

let try_empty_pat pat slice cxt env =
  match (pattern_variables pat) with
  | [] ->
     let structure =  plug_str (cxt slice, Empty) in
     if print_slice && !on_pat_slice then
       Format.fprintf ppf "@[~try_empty_pat~: %a@]@." Pprintast.structure structure; 
     (try (ignore(Typemod.type_structure env structure Location.none); false) with
     | _ ->  true)
  | (*fst :: rest*)_ ->
     false

let get_slice_pat pat slice cxt env prefix =
  let cxt'= unconstraint_pat pat Empty in
  let cxt'= plug_cxt cxt cxt' in
  let structure = plug_str (slice, cxt') in
  let (structure', _, (*env'*)_) = (try(Typemod.type_structure env
structure Location.none) with _ -> raise Pat_slice_error) in

  match structure'.str_items with
    {str_desc = Tstr_eval ({ exp_type = typ }, _)} :: [] ->
    (* Ctype.occur_in env' typ *)
    let (env'', typ') = collect ((slice, cxt'), env, prefix) typ in

    let rec filter env t = match env with
      | [] -> []
      | (str_cxt, typ) :: rest ->
         if Ctype.occur_in Env.empty typ t
         then filter rest t
         else str_cxt :: (filter rest t) in

    let rec loop1 env t = match env with
      | [] -> false
      | (_, typ) :: rest ->
         (if Ctype.occur_in Env.empty t typ then true else loop1 rest t) in

    let rec loop env checked_env = match env with
      | (str_cxt, typ') :: rest ->
(if (Ctype.moregeneral Env.empty false typ' (Btype.newgenvar ())) then
           (
if loop1 (rest @ checked_env) typ'
            then loop rest ((str_cxt, typ') :: checked_env)
   else (str_cxt, typ') :: (loop rest ((str_cxt, typ') :: checked_env)))
else (loop rest ((str_cxt, typ') :: checked_env)))
      | [] -> [] in

    let checked_env = (loop env'' []) in
    let patvals = List.map (fun ((st, _), _, _) -> st) (filter
checked_env typ') in
    (* let patvals =
      List.map (
          fun ((st, _), _ ,_ ) -> st)(
                 List.map fst (
                            List.filter (
                                function
                                | (_, ({desc = Tvar _} as typ1)) ->
                                   List.exists (
                                       fun ((*str_cxt*)_, typ2) ->
                                       Ctype.occur_in Env.empty typ1 typ2
                                     ) env''
                                | ((*str_cxt, typ1*)_, _) -> false
                              ) env'')) in *)
    List.fold_left (fun p v -> replace_pat v p) pat patvals
  | _ -> failwith "TypeDebugger: Error in judge"

(* let dummy_empty = Empty *)
(* let dummy_let = Let (Nonrecursive, [], dummy_empty) *)


(* slice のプログラム *)




(* abst_one で必要な関数 *)
(*

(*
let dummy_vb vb = map_vb hole_of_exp id vb
and dummy_case case = map_case hole_of_exp id case
and dummy_le le = map_le hole_of_exp id le
 *)
(* check_dummy : expression -> expression -> expression list
                 -> expression_desc -> expression list *)
and check_dummy e1 e2 es d =
  (* e1 が □ でなければ e2 の pexp_desc を d に置き換えた要素を追加 *)
  es @ (if e1 = hole_of_exp e1 then [] else [desc_to_exp d e2])
(*  if e1 = dummy_assertfalse e1 then es else (desc_to_exp d e2 :: es) *)
(* get_slice で必要な関数 *)
(*
let acc_e e = Map.set_exp Map.e1 e
let acc_v v = Map.set_exp Map.v1 v
let acc_c c = Map.set_exp Map.c1 c
let acc_l l = Map.set_exp Map.le l
 *)
(* abst_inside : ('a -> 'a) -> 'a list -> 'a list -> 'a list -> 'a list -> 'a list *)
(* expression を含む構文の要素の抽象化を試みて、□にならなかったものを返す *)
let rec abst_inside map1 acc forward backword = match backword with
  | [] -> List.rev acc
  | tar :: backword' ->
     (* チェック済 *)
     let forward' = forward @ [tar] in
     (* tar を□で置き換えることを試みる *)
     let dummy = map1 hole_of_exp id tar in
     let acc' =
       if tar = dummy then acc else (forward @ (dummy :: backword')) :: acc in
     abst_inside map1 acc' forward' backword'

let abst_list map1 xs = abst_inside map1 [] [] xs

(* abst_one : slice -> slice list *)
(* 抽象化の本体 *)
let abst_one exp =

  let to_exp fd e xs = Desc.to_exp fd xs e exp in
  let dummy_apply es =
    Desc.e_apply (List.map (fun e -> (Nolabel, e)) es) skeleton' in

  (* exp の構文で置き換えるようにする *)
  let abst_some e d = check_dummy e exp [] d in
  let abst_all ?(es = []) ?(e = skeleton') map1 fd xs =
    check_dummy
      e exp
      (List.map (to_exp fd e) (abst_list map1 xs))
      (if es = [] then fd xs (hole_of_exp e) else dummy_apply es) in

(*
  let abst_check_dummy' e xs fd_xs =
    check_dummy e exp xs (fd_xs (hole_of_exp e)) in

  let abst_all ?(use_dummy = None) ?(e = skeleton') map1 fd xs =
    abst_check_dummy'
      e (List.map (to_exp fd e) (abst_list map1 xs))
      (match use_dummy with
         None -> fd xs
       | Some (fd') -> fd') in
 *)

  (* acc, forward はループの始めでは [] *)
  (* abst_one のメイン部分 *)
  match exp.pexp_desc with
  | Pexp_let (flg, vs, e) ->
     (* let 文 *)
     (* let x = S1 in S2 => [let x = □ in S2; let x = S1 in □] *)
(*
     let d = Pexp_let (flg, vs, hole_of_exp e) in
     let list =
       List.map (fun vs' -> desc_to_exp (Pexp_let (flg, vs', e)) exp
                ) (abst_list Map.v1 vs) in
     abst_check_dummy e list d*)
     abst_all ~e Map.v1 (Desc.e_let flg) vs

  | Pexp_apply _ ->
     (* 基本これにした方が良いかも *)
     Desc.fold_exp (
         fun acc e ->
         if e = hole_of_exp e then acc
         else
           Desc.map_exp
             (fun e' -> if e = e' then hole_of_exp e else e')
             exp :: acc
       ) [] exp

(*
  | Pexp_apply (e, les) ->
     (* 関数適用 *)
     (* @ S1 .. Sn => [=@ S1..Sn; @ □..Sn; ...; @ S1..□]  *)
     abst_all ~e Map.le Desc.e_apply les
 *)
(*
     let d = Pexp_apply (hole_of_exp e, les) in
     let list =
       List.map (fun les' -> desc_to_exp (Pexp_apply (e, les')) exp
                ) (abst_list Map.le les) in
     abst_check_dummy e list d
 *)
  | Pexp_fun (l, eop, p, e) ->
     (* fun文 *)
     (* λx.S => λx.□ *)
(*
     let d = Pexp_fun (l, None, p, hole_of_exp e) in
     abst_check_dummy e [] d
 *)
     abst_some e (Desc.e_fun l eop p (hole_of_exp e))
  | Pexp_construct (lid, Some (e)) ->
     (* コンストラクタ *)
     (* 引数が単数か複数かで分岐 *)
     let es = match e.pexp_desc with
         Pexp_tuple es -> es
       | _ -> [] in
     abst_all
       ~es ~e Map.e1 (Desc.e_construct lid) es

(*
     begin
       match e.pexp_desc with
       | Pexp_tuple (es) ->
          let d = Pexp_apply (skeleton', List.map (fun e -> (Nolabel, e)) es) in
          let list = List.map (fun es' -> desc_to_exp (Pexp_construct (l, Some (desc_to_exp (Pexp_tuple (es')) e))) exp) (abst_list Map.e1 es) in
          abst_check_dummy e list d
       | _ ->
          let d = Pexp_construct (l, Some (hole_of_exp e)) in
          abst_check_dummy e [] d
     end
 *)
  | Pexp_match (e, cs) ->
     (* match 文 *)
     (* パターンする式と結果のみを対象にしている *)
     (* match S0 with P1 -> S1 | ... | Pn -> Sn =>
      [match □ with ...; ... with P1 -> □ | ...; ... with ... | Pn -> □] *)
     abst_all ~e Map.c1 Desc.e_match cs
(*
     let d = Pexp_match (hole_of_exp e, cs) in
     (* 式の抽象化 *)
     let list =
       List.map (
           fun cs' -> desc_to_exp (Pexp_match (e, cs')) exp
         ) (abst_list Map.c1 cs) in
     (* パターンの抽象化 *)
     abst_check_dummy e list d
 *)
  | Pexp_try (e, cs) ->
     (* try 文 *)
     (* パターンする式と結果のみを対象にしている *)
     (* try S0 with P1 -> S1 | ... | Pn -> Sn =>
      [try □ with ...; ... with P1 -> □ | ...; ... with ... | Pn -> □] *)
     abst_all ~e Map.c1 Desc.e_try cs
(*
     let d = Pexp_try (hole_of_exp e, cs) in
     let list =
       List.map (fun cs' -> desc_to_exp (Pexp_try (e, cs')) exp
                ) (abst_list Map.c1 cs) in
     abst_check_dummy e list d
 *)
  | Pexp_tuple (es) ->
     (* tuple *)
     (* (S1, ... Sn) => [(□, ... Sn); ... ; (S1, ..., □); @= S1 ,..., Sn] *)
     abst_all ~es Map.e1 Desc.e_tuple es
(*
     let d = Pexp_apply (skeleton', List.map (fun e -> (Nolabel, e)) es) in
     let list =
       List.map (fun es' -> desc_to_exp (Pexp_tuple (es')) exp
                ) (abst_list Map.e1 es) in
     abst_check_dummy skeleton' list d
 *)
  | Pexp_record (les, eop) ->
     (* record *)
     (* 各フィールドを対象にしている *)
     abst_all
       ~e:(match eop with None -> skeleton' | Some e -> e)
       Map.le Desc.e_record les
(*
     List.map (fun les' -> desc_to_exp (Pexp_record (les', None)) exp
              ) (abst_list Map.le les)
 *)
  | Pexp_array (es) ->
     (* array *)
     abst_all ~es Map.e1 Desc.e_array es
(*
     let d = Pexp_apply (skeleton', List.map (fun e -> (Nolabel, e)) es) in
     let list =
       List.map (fun es' -> desc_to_exp (Pexp_array (es')) exp
                ) (abst_list Map.e1 es) in
     abst_check_dummy skeleton' list d
 *)
  | Pexp_ifthenelse (e1, e2, eop) ->
     (* ifthenelse *)
     (* [if □ then e2 else e3; if e1 then □ else e3; if e1 then e2 else □] *)
     let fd sel =
       Desc.e_ifthenelse
         (if sel = 1 then hole_of_exp e1 else e1)
         (if sel = 2 then hole_of_exp e2 else e2)
         (match eop with
            Some (e3) when sel = 3 -> Some (hole_of_exp e3)
          | _ -> eop) in
     (abst_some e1 (fd 1)) @ (abst_some e2 (fd 2))
     @ (match eop with None -> [] | Some e3 -> abst_some e3 (fd 3))
(*
     abst_check_dummy e1 [] (Pexp_ifthenelse (hole_of_exp e1, e2, e3))
     @ abst_check_dummy e2 [] (Pexp_ifthenelse (e1, hole_of_exp e2, e3))
     @ begin
         match e3 with
         | Some (e) ->
            abst_check_dummy e [] (Pexp_ifthenelse (e1, e2, Some (hole_of_exp e)))
         | None -> []
       end
 *)
  (* sequence *)
  | Pexp_constraint (e, c) ->
     (* constraint *)
     (* [(□ : c)] *)
     abst_all ~e Map.e1 (Desc.e_constraint c) []
(*
     abst_check_dummy e [] (Pexp_constraint (hole_of_exp e, c))
 *)
(*  | Pexp_constant _ -> [exp] *)
  | _ ->
     (* 部分式がない式・対応していない式はすべて[]を返すように変更 *)
     (* 下のif文は□の型推論もやってしまっていた *)
     (*if exp = hole_of_exp exp then [] else [hole_of_exp exp]*)
     []
 *)

(*
(* search *)
(* search : (slice list * (slice -> slice) * (unit -> slice)) -> Env.t -> slice *)
let rec search (slices, cxt, f) env pat_cxt =
  match slices with
  | [] ->
     let ret = f () in
     if print_slice
     then (Format.fprintf ppf "@[  return: %a@]@."
           print_deb_exp ret);
     ret
  | first :: rest ->
     if print_slice
     then (Format.fprintf ppf "@[  first: %a@]@."
           print_deb_exp first);
     try
       (* Warnings.parse_options false "-A"; *)
       let structure = [Str.eval (cxt first)] in
       ignore (
           Typemod.type_structure env structure Location.none
         );
       (* Warnings.parse_options false Warnings.defaults_w; *)
       (* welltyped *)
       if print_slice
       then (Format.fprintf ppf "@[  welltyped : %a@]@."
                            print_deb_exp (cxt first);
             Format.fprintf ppf "@[~search~@]@.");
       search (rest, cxt, f) env pat_cxt
     with
     | Typetexp.Error _
     | Typecore.Error _ ->
        (* illtyped *)
        (* Warnings.parse_options false Warnings.defaults_w; *)
        if print_slice
        then (Format.fprintf ppf "@[  illtyped : %a@]@."
                             print_deb_exp (cxt first);
              Format.fprintf ppf "@[~get_slice~@]@.");
       get_slice (first, cxt) env pat_cxt

(* get_slice *)
(* (slice * (slice -> slice)) -> Env.t -> slice *)
and get_slice (slice, cxt) env pat_cxt =
  (* 抽象化する *)
  let abst =
    let lst = abst_one slice in
    if print_slice then
      (Format.fprintf ppf "@[~abst_one~@]@.";
       List.iter (
           fun a -> Format.fprintf ppf "@[  %a@]@." print_deb_exp a
         ) lst;
       Format.fprintf ppf "@[~search~@]@.");
    lst in
  (* search に渡す *)
  let make_thunk lst fun_acc fun_all fun_one fun_desc =
    (* s_all : 全てのリストの処理が終わった後の仕上げで必要な関数 *)
    (* s_one : 着目している式での処理を行う関数 *)
    (* fun_desc : acc と s_all を与えると desc が求まる関数 *)
    (* 各構文での処理中では、上の順番で定義する *)
    let rec slice_loop lst acc = match lst with
      | [] ->
         let s_all = get_slice' (fun_all acc) env pat_cxt in
         let d = fun_desc acc s_all in
         desc_to_exp d slice
      | first :: rest ->
         let s_one = get_slice' (fun_one first rest acc) env pat_cxt in
         slice_loop rest (acc @ [fun_acc first s_one]) in
    (* ここでサンクを作る *)
    fun () -> slice_loop lst [] in
  (* スライスを求める部分の本体 *)
  match slice.pexp_desc with
  | Pexp_let (flg, vs, e) -> (* let文 *)
     let fun_all acc =
       (e, (fun y -> cxt (desc_to_exp (Pexp_let (flg, acc, y)) slice))) in
     let fun_one vb _ acc =
       (vb.pvb_expr, (fun y -> cxt (desc_to_exp (Pexp_let (flg, acc @ [acc_v vb y], e)) slice))) in
     let fun_desc acc s_all = Pexp_let (flg, acc, s_all) in
     search (abst, cxt, make_thunk vs acc_v fun_all fun_one fun_desc) env pat_cxt
(*
     let rec loop vs a = match vs with
       | [] ->
          let sn' =
            get_slice' (e, (fun y -> cxt (desc_to_exp (Pexp_let (flg, a, y)) slice))) env pat_cxt in
          desc_to_exp (Pexp_let (flg, a, sn')) slice
       | {pvb_pat = p; pvb_expr = sn; pvb_attributes = atrs; pvb_loc = l} as vb :: rest ->
          let s' = get_slice' (sn, (fun y -> cxt (desc_to_exp (Pexp_let (flg, a @ [acc_v vb y], e)) slice))) env pat_cxt in
          loop rest (a @ [{pvb_pat = p; pvb_expr = s'; pvb_attributes = atrs; pvb_loc = l}]) in
     search (abst, cxt, fun () -> loop vs []) env pat_cxt
 *)
  | Pexp_apply (e, les) ->
     (* 関数適用 *)
     let fun_all acc =
       (e, (fun x -> cxt (desc_to_exp (Pexp_apply (x, acc)) slice))) in
     let fun_one (l, sn) rest acc =
       (sn, (fun y -> cxt (desc_to_exp (Pexp_apply (get_slice' (fun_all les) env pat_cxt, (acc @ [(l, y)] @ rest))) slice))) in
     let fun_desc acc s_all = Pexp_apply (s_all, acc) in
(*
     let rec loop les a = match les with
         [] -> desc_to_exp (Pexp_apply (s0', a)) slice
       | (l, sn) :: rest ->
          let s' =
            get_slice' (sn, (fun x -> cxt (desc_to_exp (Pexp_apply (s0', a @ [(l, x)] @ rest)) slice))) env in
          loop rest (a @ [(l, s')]) in *)
     search (abst, cxt, make_thunk les acc_l fun_all fun_one fun_desc) env pat_cxt
  | Pexp_match (e, cs) ->
     (* サンクを作る *)
     let fun_all acc =
       (e, (fun x -> cxt (desc_to_exp (Pexp_match (x, acc)) slice))) in
     let fun_one c rest acc =
       (c.pc_rhs, (fun x -> cxt (desc_to_exp (Pexp_match (get_slice' (fun_all cs) env pat_cxt, (acc @ [acc_c c x] @ rest))) slice))) in
     let fun_desc acc s_all = Pexp_match (s_all, acc) in
     let slice' = search (abst, cxt, make_thunk cs acc_c fun_all fun_one fun_desc) env pat_cxt in
     if not (!on_pat_slice)
     then slice'
     else
     begin
       match slice'.pexp_desc with
       | Pexp_match (e, cs) ->
          if print_slice && !on_pat_slice then
            Format.fprintf ppf "@[~get_slice_pat~: %a@]@." Pprintast.expression slice';
          let cs' = List.map (fun c -> try ({pc_lhs = get_slice_pat c.pc_lhs c.pc_rhs pat_cxt env []; pc_guard = c.pc_guard; pc_rhs = c.pc_rhs}) with Pat_slice_error -> c) cs in
          let rec loop cs acc = match cs with
            | [] -> List.rev acc
            | {pc_lhs = p; pc_guard = g; pc_rhs = e'} :: rest ->
              let emp_pat = ({pc_lhs = desc_to_pat Ppat_any p; pc_guard = g; pc_rhs = e'}) in
               if try_empty_pat p (desc_to_exp (Pexp_match (e, (acc @ [emp_pat] @ rest))) slice') cxt env
               then loop rest (acc @ [emp_pat])
               else loop rest (acc @ [{pc_lhs = p; pc_guard = g; pc_rhs = e'}])  in
          let cs' = loop cs' [] in
          desc_to_exp (Pexp_match (e, cs')) slice'
       | _ -> assert false
     end
(*
     let slice' = search (abst, cxt, (* fun () -> loop cs [] *) make_thunk cs acc_c fun_all fun_one fun_desc) env in
     begin
       match slice'.pexp_desc with
       | Pexp_match (e', cs') ->
       if Debug_core.print_slice && !Debug_core.on_pat_slice then
         Format.fprintf ppf "@[~get_slice_pat~: %a@]@." Pprintast.expression slice';
       if (not !Debug_core.on_pat_slice)
       then slice' (* let文の定義の中、もしくは *)
       else desc_to_exp (Pexp_match (e', List.map (fun {pc_lhs = p; pc_guard = g; pc_rhs = e} -> {pc_lhs = get_slice_pat p e Empty env []; pc_guard = g; pc_rhs = e}) cs')) slice'
       | _ -> assert false
     end
 *)
(* =======
     let slice' =
       search (abst, cxt, (* fun () -> loop cs [] *) make_thunk cs acc_c fun_all fun_one fun_desc) env in
     slice'

>>>>>>> Stashed changes *)
  | Pexp_try (e, cs) ->
     (* try 文 *)
     (* ほぼ match と同じ *)
     let fun_all acc =
       (e, (fun x -> cxt (desc_to_exp (Pexp_try (x, acc)) slice))) in
     let fun_one c rest acc =
       (c.pc_rhs, (fun x -> cxt (desc_to_exp (Pexp_try (get_slice' (fun_all cs) env pat_cxt, (acc @ [acc_c c x] @ rest))) slice))) in
     let fun_desc acc s_all = Pexp_try (s_all, acc) in
     search (abst, cxt, make_thunk cs acc_c fun_all fun_one fun_desc) env pat_cxt
  | Pexp_fun (l, None, p, e) ->
     (* 関数 *)
     (* λx.S => λx.□ *)
     let pat_cxt' = unconstraint_pat p Empty in
     let pat_cxt'= plug_cxt pat_cxt pat_cxt' in
     let slice' = search (abst, cxt, (fun () -> desc_to_exp (Pexp_fun (l, None, p, get_slice' (e, (fun y -> cxt (desc_to_exp (Pexp_fun (l, None, p,  y)) slice))) env pat_cxt')) slice)) env pat_cxt' in
     if not (!on_pat_slice)
     then slice'
     else
     begin
     match slice'.pexp_desc with
     | Pexp_fun (l, None, p, e) ->
       if print_slice && !on_pat_slice then
         Format.fprintf ppf "@[~get_slice_pat~: %a@]@." Pprintast.expression slice';
       (* if (!inner_let || (not !Debug_core.on_pat_slice))
       then slice' (* let文の定義の中、もしくは *)
       else *)
       let p' = try(get_slice_pat p e pat_cxt env [])
                with Pat_slice_error -> p in
       let slice' = (desc_to_exp (Pexp_fun (l, None, p', e)) slice') in

       let pat_empty_slice = (desc_to_exp (Pexp_fun (l, None, desc_to_pat Ppat_any p', e)) slice') in
       if (try_empty_pat p' pat_empty_slice cxt env)
       then pat_empty_slice
       else slice'
     | _ -> assert false
     end
  | Pexp_tuple (es) ->
     (* 関数適用 *)
     let fun_all _ = (skeleton', id) in
     let fun_one sn rest acc =
       (sn, (fun x -> cxt (desc_to_exp (Pexp_tuple (acc @ [x] @ rest)) slice))) in
     let fun_desc acc _ = Pexp_tuple (acc) in
     search (abst, cxt, make_thunk es acc_e fun_all fun_one fun_desc) env pat_cxt
  | Pexp_construct (l, Some (e)) ->
     (* コンストラクタ *)
     (* 引数がある場合について考える *)
     begin
       match e.pexp_desc with
       | Pexp_tuple (es) ->
          let fun_all _ = (skeleton', id) in
          let fun_one sn rest acc =
            (sn, (fun x -> cxt (desc_to_exp (Pexp_construct (l, Some (desc_to_exp (Pexp_tuple (acc @ [x] @ rest)) e))) slice))) in
          let fun_desc acc _ = Pexp_construct (l, Some (desc_to_exp (Pexp_tuple (acc)) e)) in
          search (abst, cxt, make_thunk es acc_e fun_all fun_one fun_desc) env pat_cxt
       | _ ->
          search (abst, cxt, (fun () -> desc_to_exp (Pexp_construct (l, Some (get_slice' (e, cxt) env pat_cxt))) slice)) env pat_cxt
     end
(*
     search (abst, cxt, (fun () -> desc_to_exp (Pexp_construct (l, Some (get_slice (e, cxt) env pat_cxt))) slice)) env pat_cxt
 *)
  | Pexp_record (les, None) ->
     (* レコード *)
     let fun_all _ = (skeleton', id) in
     let fun_one (l, sn) rest acc =
       (sn, (fun x -> cxt (desc_to_exp (Pexp_record (acc @ [(l, x)] @ rest, None)) slice))) in
     let fun_desc acc _ = Pexp_record (acc, None) in
     search (abst, cxt, make_thunk les acc_l fun_all fun_one fun_desc) env pat_cxt
  | Pexp_array (es) ->
     (* 配列 *)
     let fun_all _ = (skeleton', id) in
     let fun_one sn rest acc =
       (sn, (fun x -> cxt (desc_to_exp (Pexp_array (acc @ [x] @ rest)) slice))) in
     let fun_desc acc _ = Pexp_array (acc) in
     search (abst, cxt, make_thunk es acc_e fun_all fun_one fun_desc) env pat_cxt
  | Pexp_ifthenelse (e1, e2, e3) ->
     (* ifthenelse *)
     search (abst,cxt, (
                   fun () ->
                   let s1' =
                     get_slice' (e1, (fun y -> cxt (desc_to_exp (Pexp_ifthenelse (y, e2, e3)) slice))) env pat_cxt in
                   let s2' =
                     get_slice' (e2, (fun y -> cxt (desc_to_exp (Pexp_ifthenelse (s1', y, e3)) slice))) env pat_cxt in
                   let s3' =
                     match e3 with
                     | None -> None
                     | Some (e3') ->
                        Some (get_slice' (e3', (fun y -> cxt (desc_to_exp (Pexp_ifthenelse (s1', s2', Some (y))) slice))) env pat_cxt) in
                   desc_to_exp (Pexp_ifthenelse (s1', s2', s3')) slice)) env pat_cxt
(*
  | Pexp_ident _ -> slice    (* 変数 *)
  | Pexp_constant _ -> slice (* 定数 *)
  | Pexp_variant _ -> slice
 *)
  | _ -> slice
(* get_slice' *)
and get_slice' (slice, cxt) env pat_cxt =
  if slice = hole_of_exp slice
  then slice
  else get_slice (slice, cxt) env pat_cxt

(* judge : expression context_t -> yes_no_list * type_expr *)
let judge ((expr, cxt), env, prefix) =
  let structure = plug_str (expr, cxt) in
  let (structure', _, _) = Typemod.type_structure env structure Location.none in
  match structure'.str_items with
    {str_desc = Tstr_eval ({ exp_type = typ }, _)} :: [] ->
      collect ((expr, cxt), env, prefix) typ
  | _ -> failwith "TypeDebugger: Error in judge"
 *)
(*
let get_type_expr ((expr, cxt), env, prefix) =
  try
    (* expr(fun文)の型を求める *)
    let (_, typ) = judge ((expr, cxt), env, prefix) in
    begin
      match split_arrow typ with
      | Some (t, _) -> Some (t)
      | None -> Some (typ)
    end
  with _ -> None (* Noneが返されるということは、矢印でなかったもしくはエラー *)

(* レコードの補完 *)
(* complete_pat_record : expression context_t
   -> (Longident.t loc * pattern) list -> pattern_desc *)
let complete_pat_record ((expr, cxt), env, prefix) (lps, flg) =
  match get_type_expr ((expr, cxt), env, prefix) with
  | None -> Ppat_any
  | Some (dummy_t) ->
     (* レコードのパターンの置き換えを行う *)
     (* 各フィールドのダミーを作る *)
     let dummy_lps =
       List.map (
           fun {pld_name = {txt = t; loc = l}} ->
           ({txt = Longident.parse t; loc = l}, wildcard)
         ) (decode_labels dummy_t prefix) in
     (* lps の要素を順に dummy_lps に当てはめていく *)
     let lps' =
       List.fold_left (
           (* lst : 置き換えの対象 *)
           (* (ln, pn) : パターン中の一要素 *)
           fun lst (ln, pn) ->
           List.map (
               fun (lm, pm) ->
               if Longident.last lm.txt = Longident.last ln.txt
               then (ln, pn) else (lm, pm)) lst
         ) dummy_lps lps in
     (* record の desc を返す *)
     Ppat_record (lps', flg)

let dummy_fun pat =
  desc_to_exp (Pexp_fun (Nolabel, None, pat, skeleton')) skeleton'

let rec complete_pat ((expr, cxt), env, prefix) pat = match pat.ppat_desc with
  | Ppat_any -> pat
  | Ppat_var _ -> pat
  | Ppat_alias (p, loc) ->
     let p' = complete_pat ((expr, cxt), env, prefix) p in
     let d = Ppat_alias (p', loc) in
     desc_to_pat d pat
  | Ppat_constant _ -> pat
  | Ppat_interval _ -> pat
  | Ppat_tuple (ps) ->
     let ps' = List.map (
                   fun pn -> complete_pat ((expr, cxt), env, prefix) pn) ps in
     let d = Ppat_tuple (ps') in
     desc_to_pat d pat
  | Ppat_record (lps, flg) ->
     (* レコード *)
     (* 足りないフィールドを補う *)
     let d = complete_pat_record ((expr, cxt), env, prefix) (lps, flg) in
     desc_to_pat d pat
  | Ppat_or (p1, p2) ->
     let p1' = complete_pat ((expr, cxt), env, prefix) p1 in
     let p2' = complete_pat ((expr, cxt), env, prefix) p2 in
     let d = Ppat_or (p1', p2') in
     desc_to_pat d pat
  | _ -> pat

let rec sort_vb env vs = match vs with
  | [] -> []
  | first :: rest ->
     (* first のみで定義した関数がエラーになるかどうかをチェック *)
     try
       ignore (Typemod.type_structure env [Str.value Recursive [first]] Location.none); first :: sort_vb env rest
     with
     | _ -> (sort_vb env rest) @ [first]

let rec complete ((expr, cxt), env, prefix) =  match expr.pexp_desc with
  | Pexp_ident _ -> expr
  | Pexp_constant _ -> expr
  | Pexp_let (flg, vs, exp) ->
     let exp' = complete ((exp, cxt), env, prefix) in
     let vs' =
       List.map (map_vb (fun e -> complete ((e, cxt), env, prefix)) id) vs in
     let d' = Pexp_let (flg, sort_vb env vs', exp') in
     desc_to_exp d' expr
  | Pexp_function cs ->
     (* function | P1 -> E1 | ... *)
     (* csに含まれるパターン全てに対して同じように処理する *)
     let cs' =
       List.map (
           let fe = fun e -> complete ((e, cxt), env, prefix) in
           let fp = fun p -> complete_pat ((dummy_fun p, cxt), env, prefix) p in
           map_case fe fp) cs in
     let d' = Pexp_function (cs') in
     desc_to_exp d' expr
  | Pexp_fun (l, eop, pat, exp) ->
     (* fun P -> E *)
     (* Pの型をチェックする *)
     let pat' = complete_pat ((dummy_fun pat, cxt), env, prefix) pat in
     let exp' = complete ((exp, cxt), env, prefix) in
     let d' = Pexp_fun (l, eop, pat', exp') in
     desc_to_exp d' expr
  | Pexp_apply (e0, les) ->
     (* E0 E1 E2 ... *)
     let e0' = complete ((e0, cxt), env, prefix) in
     let les' =
       List.map (map_le (fun en -> complete ((en, cxt), env, prefix)) id) les in
     let d' = Pexp_apply (e0', les') in
     desc_to_exp d' expr
  | Pexp_match (e, cs) ->
     (* match E0 with P1 -> E1 | ... *)
     (* csに含まれるパターン全てに対して同じように処理する *)
     let e' = complete ((e, cxt), env, prefix) in
     let cs' =
       List.map (
           let fe = fun e -> complete ((e, cxt), env, prefix) in
           let fp = fun p -> complete_pat ((dummy_fun p, cxt), env, prefix) p in
           map_case fe fp) cs in
     let d' = Pexp_match (e', cs') in
     desc_to_exp d' expr
  | Pexp_try (e, cs) ->
     (* try E0 with P1 -> E1 | ... *)
     (* csに含まれるパターン全てに対して同じように処理する *)
     let e' = complete ((e, cxt), env, prefix) in
     let cs' =
       List.map (
           let fe = fun e -> complete ((e, cxt), env, prefix) in
           let fp = fun p -> complete_pat ((dummy_fun p, cxt), env, prefix) p in
           map_case fe fp) cs in
     let d' = Pexp_try (e', cs') in
     desc_to_exp d' expr
  | Pexp_tuple (es) ->
     let es' = List.map (fun en -> complete ((en, cxt), env, prefix)) es in
     let d' = Pexp_tuple (es') in
     desc_to_exp d' expr
  | Pexp_construct (lid, Some (e)) ->
     let e' = complete ((e, cxt), env, prefix) in
     let d' = Pexp_construct (lid, Some (e')) in
     desc_to_exp d' expr
  | Pexp_variant (l, Some (e)) ->
     let e' = complete ((e, cxt), env, prefix) in
     let d' = Pexp_variant (l, Some (e')) in
     desc_to_exp d' expr
  | Pexp_record (les, eop) ->
     let les' =
       List.map (
           map_le (fun en -> complete ((en, cxt), env, prefix)) id
         ) les in
     let eop' = match eop with
       | None -> None
       | Some (e) -> Some (complete ((e, cxt), env, prefix)) in
     let d' = Pexp_record (les', eop') in
     desc_to_exp d' expr
  | Pexp_field (e, lid) ->
     let e' = complete ((e, cxt), env, prefix) in
     let d' = Pexp_field (e', lid) in
     desc_to_exp d' expr
  | Pexp_setfield (e1, lid, e2) ->
     let e1' = complete ((e1, cxt), env, prefix) in
     let e2' = complete ((e2, cxt), env, prefix) in
     let d' = Pexp_setfield (e1', lid, e2') in
     desc_to_exp d' expr
  | Pexp_array (es) ->
     let es' = List.map (fun en -> complete ((en, cxt), env, prefix)) es in
     let d' = Pexp_array (es') in
     desc_to_exp d' expr
  | Pexp_ifthenelse (e1, e2, eop) ->
     let e1' = complete ((e1, cxt), env, prefix) in
     let e2' = complete ((e2, cxt), env, prefix) in
     let eop' = match eop with
       | None -> None
       | Some (e) -> Some (complete ((e, cxt), env, prefix)) in
     let d' = Pexp_ifthenelse (e1', e2', eop') in
     desc_to_exp d' expr
  | Pexp_sequence (e1, e2) ->
     let e1' = complete ((e1, cxt), env, prefix) in
     let e2' = complete ((e2, cxt), env, prefix) in
     let d' = Pexp_sequence (e1', e2') in
     desc_to_exp d' expr
  | _ -> expr
 *)
(*
module Pattern_slicing : sig
end = struct
end
 *)


module Complete = struct

  let dummy_fun pat =
    desc_to_exp (Pexp_fun (Nolabel, None, pat, skeleton')) skeleton'

  (* pattern complete *)
  let rec pattern ((pat, cxt), env, prefix) =

    (* パターンに対する補完を行う *)
    let pat' p = go pattern prefix env cxt p in

    let desc d = desc_to_pat d pat in
    let map1 y1 ys = List.map (y1 id pat') ys in
    let to_pat fd fy ?(p = wildcard) ys =
      Desc.to_pat fd (fy ys) (pat' p) pat in

    match pat.ppat_desc with
    | Ppat_any -> pat
    | Ppat_var _ -> pat
    | Ppat_alias (p, lid) ->
       to_pat (Desc.p_alias lid) id ~p []
    | Ppat_constant _ -> pat
    | Ppat_interval _ -> pat
    | Ppat_tuple (ps) ->
       to_pat Desc.p_tuple (map1 Map.p1) ps
(*
       desc (Ppat_tuple (List.map pat' ps)) *)
    | Ppat_construct (lid, Some (p)) ->
       to_pat (Desc.p_construct lid) id ~p []
    | Ppat_variant (l, Some (p)) ->
       to_pat (Desc.p_variant l) id ~p []

    | Ppat_record (lps, flg) ->
       (* レコード *)
       (* 足りないフィールドを補う *)
       let lps' =
         try
           let (_, exp_typ) = judge ((dummy_fun pat, cxt), env, prefix) in
           let pat_typ = match split_arrow exp_typ with
               Some (t, _) -> t
             | None -> exp_typ in
           if print_slice then
             Format.fprintf ppf "@[  make dummy labels: type %a @]@."
                            Printtyp.type_expr pat_typ;

           let dummy_lps =
             List.map (
                 fun {pld_name = {txt = t; loc = l}} ->
                 ({txt = Longident.parse t; loc = l}, wildcard)
               ) (decode_labels pat_typ prefix) in

           List.fold_left (
               fun lst (ln, pn) ->
               List.map (
                   fun (lm, pm) ->
                   if Longident.last lm.txt = Longident.last ln.txt
                   then (ln, pn) else (lm, pm)) lst
             ) dummy_lps lps
         with
           _ -> lps in
       to_pat (Desc.p_record flg) (map1 Map.lp) lps'

(*
       desc (Ppat_record (lps', flg))
 *)
    | Ppat_array (ps) ->
       to_pat Desc.p_array (map1 Map.p1) ps
    | Ppat_or (p1, p2) ->
       desc (Ppat_or (pat' p1, pat' p2))
    | Ppat_constraint (p, c) ->
       to_pat (Desc.p_constraint c) id ~p []
    | _ -> pat

  (* expression complete *)
  let rec expression ((expr, cxt), env, prefix) =

    let go' f x = go f prefix env cxt x in
    let exp' e = go' expression e in
    let pat' p = go' pattern p in

    (* 式に対する補完を行う *)
    let desc d = desc_to_exp d expr in
    let map1 x1 xs = List.map (x1 exp' pat') xs in
    let to_exp fd fx ?(e = skeleton') xs =
      Desc.to_exp fd (fx xs) (exp' e) expr in

    match expr.pexp_desc with
    | Pexp_let (flg, vs, e) ->
       to_exp (Desc.e_let flg) (go' value_bindings) ~e vs
(*
       let vs' = go' value_bindings vs in
       let d' = Pexp_let (flg, vs', exp' e) in
       desc d'
 *)
    | Pexp_function cs ->
       (* function | P1 -> E1 | ... *)
       (* csに含まれるパターン全てに対して同じように処理する *)
       to_exp Desc.e_function (go' cases) cs
(*
       let d' = Pexp_function (go' cases cs) in
       desc d'
 *)
    | Pexp_fun (l, eop, p, e) ->
       (* fun P -> E *)
       (* Pの型をチェックする *)
       let d' = Pexp_fun (l, eop, pat' p, exp' e) in
       desc d'
    | Pexp_apply (e, les) ->
       (* E0 E1 E2 ... *)
       to_exp Desc.e_apply (map1 Map.le) ~e les
(*
       let les' = List.map (Map.le exp' id) les in
       let d' = Pexp_apply (exp' e, les') in
       desc d'
 *)
    | Pexp_match (e, cs) ->
       (* match E0 with P1 -> E1 | ... *)
       (* csに含まれるパターン全てに対して同じように処理する *)
       to_exp Desc.e_match (go' cases) ~e cs
(*
       let cs' = List.map (Map.c1 exp' pat') cs in
       let d' = Pexp_match (exp' e, cs') in
       desc d'
 *)
    | Pexp_try (e, cs) ->
       (* try E0 with P1 -> E1 | ... *)
       (* csに含まれるパターン全てに対して同じように処理する *)
       to_exp Desc.e_try (go' cases) ~e cs
(*
       let cs' = List.map (Map.c1 exp' pat') cs in
       let d' = Pexp_try (exp' e, cs') in
       desc d'
 *)
    | Pexp_tuple (es) ->
       to_exp Desc.e_tuple (map1 Map.e1) es
(*
       desc (Pexp_tuple (List.map exp' es))
 *)
    | Pexp_construct (lid, Some (e)) ->
       to_exp (Desc.e_construct lid) id ~e []
(*
       let d' = Pexp_construct (lid, Some (exp' e)) in
       desc d'
 *)
    | Pexp_variant (l, Some (e)) ->
       to_exp (Desc.e_variant l) id ~e []
(*
       let d' = Pexp_variant (l, Some (exp' e)) in
       desc d'
 *)
    | Pexp_record (les, eop) ->
       let e = match eop with
           None -> skeleton' | Some e -> e in
       to_exp Desc.e_record (map1 Map.le) ~e les
(*
       let les' = List.map (Map.le exp' id) les in
       let eop' = match eop with
         | None -> None
         | Some (e) -> Some (exp' e) in
       let d' = Pexp_record (les', eop') in
       desc d'
 *)
    | Pexp_field (e, lid) ->
       to_exp (Desc.e_field lid) id ~e []
(*
       desc (Pexp_field (exp' e, lid))
 *)
    | Pexp_setfield (e1, lid, e2) ->
(*
       let d' = Pexp_setfield (exp' e1, lid, exp' e2) in
       desc d'
 *)
       desc (Desc.e_setfield lid (exp' e1) (exp' e2))
    | Pexp_array (es) ->
       to_exp Desc.e_array (map1 Map.e1) es
(*
       desc (Pexp_array (List.map exp' es))
 *)
    | Pexp_ifthenelse (e1, e2, eop) ->
(*
       let eop' = match eop with
         | None -> None
         | Some (e3) -> Some (exp' e3) in
       let d' = Pexp_ifthenelse (exp' e1, exp' e2, eop') in *)
       desc (Desc.e_ifthenelse
               (exp' e1) (exp' e2)
               (match eop with None -> None | Some e3 -> Some (exp' e3)))
    | Pexp_sequence (e1, e2) ->
       desc (Desc.e_sequence (exp' e1) (exp' e2))
(*
       desc (Pexp_sequence (exp' e1, exp' e2))
 *)
    | _ -> expr

  and value_bindings ((vs, cxt), env, prefix) = match vs with
    | [] -> []
    | vn :: rest ->
       let vn' =
         Map.v1 (go expression prefix env cxt)
                (go pattern prefix env cxt) vn in
       (* vn のみで定義した関数がエラーになるかどうかをチェック *)
       let rest' = value_bindings ((rest, cxt), env, prefix) in
       try
         ignore (
             Typemod.type_structure
               env [Str.value Recursive [vn']] Location.none);
         vn' :: rest'
       with
       | _ -> rest' @ [vn']

  and cases ((cs, cxt), env, prefix) =
    List.map (Map.c1 (go expression prefix env cxt)
                     (go pattern prefix env cxt)) cs
end


module Slice : sig
  type 'a t
  val slice : 'a t -> 'a
  val cnt : 'a t -> int
  val time : 'a t -> float
  val set : 'a -> int -> float -> 'a t
end = struct
  type 'a t = {slice : 'a; cnt : int; time : float}
  let slice s = s.slice
  let cnt s = s.cnt
  let time s = s.time
  let set slice cnt time = {slice; cnt; time}
end

module Times : sig
  (* 0 を渡すとリセット。それ以外はリストに時間を追加 *)
  val set : float -> unit
  val cnt : unit -> int
  val time : unit -> float
end = struct
  let times = ref []
  let set time =
    times := if time = 0. then [] else time :: !times
  let cnt () = List.length !times
  let time () = List.fold_left (+.) 0. !times
end

(* expression slicing *)
module ExprSlicing : sig

  val hole : expression -> expression
  val abst : bool -> expression -> expression -> expression
  val dummy_apply : expression -> expression list -> expression list

  val print : string -> int -> (string * expression) list -> unit

  (* 型推論 *)
  val typed : Env.t -> item_cxt -> expr_cxt -> expression -> bool

  val wrap_item : item_cxt -> expr_cxt -> expr_cxt -> expression -> structure
  val wrap_expr : expr_cxt -> expr_cxt -> expression -> expression

  val getTop :
    int *
      ((Parsetree.expression * ('a -> 'a)) *
         ((Parsetree.expression -> Parsetree.expression) ->
          Parsetree.expression -> Parsetree.structure) ->
       Env.t -> 'b -> Parsetree.expression) ->
    Parsetree.expression ->
    ((Parsetree.expression -> Parsetree.expression) ->
     Parsetree.expression -> Parsetree.structure) ->
    Env.t -> 'b -> Parsetree.expression

end = struct

  let print_slice = false

  let hole e = Size.reset (hole_of_exp e)

  let print' (kind, expr) =
    Format.fprintf
      ppf "@[  %s : %a@]@."
      kind print_deb_exp expr

  let print kind n lst =
    print_newline ();
    Format.fprintf
      ppf "@[~ %s %d ~@]@." kind n;
    List.iter print' lst

  let wrap_expr expr_cxt' expr_cxt expr =
    expr_cxt' (expr_cxt expr)
  let wrap_item item_cxt expr_cxt' expr_cxt expr =
    item_cxt (wrap_expr expr_cxt' expr_cxt) expr

  let dummy_apply expr es =
    if List.exists (fun e -> e = hole e) es then []
    else
      [{expr with
         pexp_desc =
           Pexp_apply (hole expr, List.map (fun e -> (Nolabel, e)) es)}]


  let abst sel e' e = match Desc.comp_loc_exp e' e with
      1 -> if sel then e else hole e
    | 0 -> e'
    | _ -> if sel then hole e else e

  include Times

(*
  (* typemod の回数 *)
  let times = ref []

  let reset () = times := []
  let getCnt () = List.length !times
  let getTime () = List.fold_left (+.) 0. !times
 *)


  let typed env item_cxt expr_cxt expr =

    let t = Sys.time () in
    try
      ignore
        (Typemod.type_structure env (item_cxt expr_cxt expr) Location.none);
      set (Sys.time () -. t);
      true
    with
      _ ->
      set (Sys.time () -. t);
      false


  (* 各々の入口 *)
  let getTop (n, g) expr item_cxt env cxt =

    if print_slice then
      print "slicing" n [];

    let slice =
      set 0.;
      if not (Desc.leaf_exp expr) then
        g ((Size.set expr, id), item_cxt) env cxt
      else if typed env item_cxt id skeleton' then
        Size.reset expr
      else
        hole expr in

    if print_slice then
      Format.fprintf
        ppf "@[sum / count : %d / %f @]@."
        (cnt ())
        (time ());

    (* デバッグモードの場合、ここで出力 *)
    slice

end


module type ExprSlicing_type = sig
(*
  val get :
    (expression * expr_cxt) * item_cxt -> Env.t -> expr_context -> expression
 *)
  val top : expression -> item_cxt -> Env.t -> expr_context -> expression

end


module ExprSlicing1 : ExprSlicing_type = struct

  (* 最もオーソドックスなスライシング *)
  (* ・着目する式の子ノードを□に置き換えられるか見ていく。 *)
  (* ・抽象化は部分式1つずつ abst_one のみ。 *)
  (* ・fold を使って葉ノード以外に対して再帰 *)

  open ExprSlicing

  let make_expr expr e' =
    Desc.map_exp (abst false e') expr


  let selected_expr expr expr_cxt' e' =
    if Desc.comp_loc_exp e' expr < 0 then expr_cxt' e' else e'

  (* dummy apply *)
  let getChildren'' expr = match expr.pexp_desc with
    | Pexp_tuple es ->
       dummy_apply expr es
    | Pexp_array es ->
       dummy_apply expr es
    | Pexp_construct (_, Some {pexp_desc = Pexp_tuple es}) ->
       dummy_apply expr es
    | _ -> []

  (* □以外の子ノード全て *)
  let getChildren' expr = match expr.pexp_desc with
    | Pexp_construct (_, Some {pexp_desc = Pexp_tuple es}) ->
       List.filter (fun e -> e <> hole e) es
    | _ ->
       Desc.fold_exp (
           fun acc e ->
           if Size.fltr0 e then e :: acc else acc
         ) [] expr

  let getChildren expr =
    if false then
      getChildren'' expr @ getChildren' expr
    else
      getChildren' expr

  let rec search (slices, expr_cxt, item_cxt, f) env cxt = match slices with
    | [] -> f ()
    | first :: rest ->
       if print_slice then
         print "search" 1 [("child", first)];
       if typed env item_cxt expr_cxt first then
         (* welltyped *)
         search (rest, expr_cxt, item_cxt, f) env cxt
       else
         (* illtyped *)
         get ((expr_cxt first, id), item_cxt) env cxt

  and get ((expr, expr_cxt), item_cxt) env cxt =

    if print_slice then
      print "get" 1 [("target", expr)];

    let children = getChildren expr in

    match expr.pexp_desc with

    | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as expr')) ->

       (* Construct *)
       let fold es' e' =
         {expr with
           pexp_desc =
             Pexp_construct (
                 lid,
                 Some {expr' with
                        pexp_desc =
                          Pexp_tuple (List.map (abst false e') es')})} in
       let f () =
         let slice =
           let fold' es' e' = fold es' (Size.reset e') in
           let es' =
             Desc.fold_exp (
                 fun es' e ->
                 let slice =
                   get' ((e, id), wrap_item item_cxt (fold' es')) env cxt in
               List.map (
                   fun e ->
                   if Desc.comp_loc_exp slice e < 0 then e else slice) es'
               ) es expr' in
           fold' es' skeleton' in
         if print_slice then
           print "get" 1 [("return", slice)];
         wrap_expr expr_cxt Size.reset slice in

       (* search *)
       search (
           children,
           wrap_expr expr_cxt (selected_expr expr (fold es)),
           item_cxt, f) env cxt

    | _ ->

       let f () =
         let slice =
           let item_cxt' = wrap_item item_cxt expr_cxt in
           Desc.fold_exp (
               fun expr' e ->
               let expr_cxt'' = make_expr expr' in
               let item_cxt'' = wrap_item item_cxt' expr_cxt'' in          
               get' ((e, id), item_cxt'') env cxt |> expr_cxt''
             ) expr expr in
         if print_slice then
           print "get" 1 [("return", slice)];
         wrap_expr expr_cxt Size.reset slice in

       (* search *)
       search (
           children,
           wrap_expr expr_cxt (selected_expr expr (make_expr expr)),
           item_cxt, f) env cxt

  (* get' *)
  and get' ((expr, expr_cxt), item_cxt) env cxt  =
    if Desc.leaf_exp expr then wrap_expr expr_cxt Size.reset expr
    else get ((expr, expr_cxt), item_cxt) env cxt

  (* top *)
  let top = getTop (1, get)

end

(* 構文ごとに小さな例を作って、結果が正しいかどうかチェック *)

module ExprSlicing2 : ExprSlicing_type = struct

  (* resize あり *)

  open ExprSlicing

  let rec search ((child, sel, expr_cxt, slice_cxt), item_cxt) env cxt =


    let sel' = typed env item_cxt (slice_cxt sel expr_cxt) child in

    if print_slice then
      print "search" 2
            [(if sel then "expect" else "one")
             ^ "/" ^ (if sel' then "welltyped" else "illtyped"), slice_cxt sel id child];

    if sel' && sel then
      (* welltyped : abst expect *)
      search ((child, false, expr_cxt, slice_cxt), item_cxt) env cxt

    else
      let g pair = get (pair, item_cxt) env cxt in

      if sel' && Size.is1 child then
        (* welltyped : is1 *)
        g (slice_cxt false expr_cxt (Size.reset child), id)

      else if sel' || sel then
        (* welltyped : greater1 *)
        (* illtyped : abst expect *)
        g (child, slice_cxt sel expr_cxt)

(*
      else if sel' then
        (* welltyped : greater1 *)
        g (child, slice_cxt sel expr_cxt)

      else if sel then 
        g (slice_cxt sel expr_cxt child, id)
 *)
      else
        (* illtyped : abst one *)
        g (slice_cxt sel id child , expr_cxt)

  and get ((expr, expr_cxt), item_cxt) env cxt =

    if Size.fltr1 expr then
      begin
        let (expr', slice_cxt) = Size.getChildSet expr in
        if print_slice then
          print "get" 2
                [("target", expr); ("child", expr')];
        search ((expr',
                 slice_cxt true id expr' <> expr, expr_cxt,
                 slice_cxt), item_cxt) env cxt
      end
    else
      begin
        let slice = get' ((expr, expr_cxt), item_cxt) env cxt in
        if print_slice then
          print "get" 2
                [("target", expr); ("return", slice)];
        slice
      end


  and get' ((expr, expr_cxt), item_cxt) env cxt =
    let slice = expr_cxt expr in
    if Size.fltr0 slice then
      get ((slice, id), item_cxt) env cxt
    else
      slice


  (* top *)
  let top = getTop (2, get)


end


module ExprSlicing3 : ExprSlicing_type = struct

  (* resize なし *)
  open ExprSlicing

  (* 置き換え関数 *)

  let replace slice expr = desc_to_exp slice.pexp_desc expr

  let replace2 slice expr =
    Size.terminated (desc_to_exp slice.pexp_desc expr)

  (* 表示用 *)
  let skeleton2 = Exp.ident (mknoloc (Longident.parse "■"))
  let show_cxt sel slice =
    if slice = skeleton' then slice
    else (
      replace skeleton2 slice
      |> if sel then Size.terminated else id)

  (* search *)
  let rec search ((children, slice_cxt, expr_cxt), item_cxt) env cxt =

    match children with
    | [] ->
       get' ((slice_cxt id true skeleton', expr_cxt), item_cxt) env cxt

    | first :: rest ->

       let n = Size.get 0 first in

       let g typed sel1 sel2 =

         let slice_cxt' f slice =
           slice_cxt
             f (typed || sel1)
             (if typed then replace2 slice first else slice) in

         let err = not typed in

         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~SEARCH~@]@.";
             
             Format.fprintf
               ppf "@[slice_cxt : @]@.";
             Format.fprintf
               ppf "  @[fun ■ -> function@]@.";

             let expr' =
               Meta.clean
                 "all" (
                   if err && sel2 then
                     slice_cxt id sel1 first
                   else
                     slice_cxt
                       id true (show_cxt true first)) in

             Format.fprintf
               ppf "  @[| (%a) -> %a@]@."
               print_deb_exp (if n < 0
                              then skeleton' else first)
               print_deb_exp expr';

             Format.fprintf
               ppf "@[%s / %s @]@."
               (if typed then "welltyped" else "illtyped")
               (if typed then
                  if sel1 && sel2 then "backtrack:"
                  else if sel2 then "breadth:"
                  else if sel1 then "depth:"
                  else "abst element:"
                else
                  if sel1 && sel2 then "no bind:"
                  else if sel2 then "abst all:"
                  else if sel1 then "abst one:"
                  else "abst expect:");

             Format.fprintf
               ppf "  @[fun ■ -> %a@]@."
               print_deb_exp (
                 slice_cxt'
                   expr_cxt (show_cxt sel1 first));
           end;

         if err && sel1 && sel2 then
           (* illtyped : no bind *)
           slice_cxt id false skeleton'

         else if err && sel1 then
           (* illtyped : abst one *)
           get ((slice_cxt' id first, expr_cxt), item_cxt) env cxt

         else if err || sel2 then
           (* illtyped : abst one / abst all / no bind / abst expect *)
           (* welltyped : backtrack / breadth *)
           let sel = (typed && sel1) || (err && (sel1 || sel2)) in
           let expr_cxt' sel = if sel then expr_cxt else id in
           get ((slice_cxt' (expr_cxt' sel) first,
                 expr_cxt' (not sel)), item_cxt) env cxt

         else if typed && sel1 then
           (* welltyped : depth *)
           get ((first, slice_cxt' expr_cxt), item_cxt) env cxt

         else
           (* welltyped : abst element *)
           search ((rest, slice_cxt, expr_cxt), item_cxt) env cxt in

       let error sel =
         assert (not (typed env item_cxt (slice_cxt expr_cxt sel) first));
         g false sel (n < 0) in
       (* 次の処理を決める *)
       try
         assert (rest <> []);
         error false
       with
         _ ->
         try
           error true
         with
           _ ->
           if n < 0 then
             g true false false
           else if 1 < n then
             g true true false
           else if rest = [] then
             g true true true
           else
             g true false true

  and get ((expr, expr_cxt), item_cxt) env cxt =

    if print_slice then
      print "get" 3
            [("target", expr)];

    if Desc.leaf_exp expr then
       (* 変数 / 定数 *)
       get' ((expr, expr_cxt), item_cxt) env cxt

    else
      match expr.pexp_desc with

      | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple _} as e)) ->
         let children = Size.children e in
         let slice_cxt expr_cxt' sel e' =
           expr_cxt'
             {expr with
               pexp_desc = 
                 Pexp_construct (lid, Some (Abst.get e sel e'))} in
         search ((children, slice_cxt, expr_cxt), item_cxt) env cxt    

      | _ ->
         let children = Size.children expr in
         let slice_cxt expr_cxt' sel e' =
           expr_cxt' (Abst.get expr sel e') in
         search ((children, slice_cxt, expr_cxt), item_cxt) env cxt

  and get' ((expr, expr_cxt), item_cxt) env _ =

    let slice =
      if Size.fltr0 expr then
        let slice' = hole expr in
        if typed env item_cxt expr_cxt slice' then
          Size.reset expr
        else
          slice'
      else
        expr_cxt expr in

    if print_slice then
      print "get" 3 [("return", slice)];

    slice

  (* top *)
  let top = getTop (3, get)

end

module ExprSlicingDebugger = struct
(*
module Slice : sig
  type 'a t
  val slice : 'a t -> 'a
  val cnt : 'a t -> int
  val time : 'a t -> float
  val set : 'a -> int -> float -> 'a t
end = struct
  type 'a t = {slice : 'a; cnt : int; time : float}
  let slice s = s.slice
  let cnt s = s.cnt
  let time s = s.time
  let set slice cnt time = {slice; cnt; time}
end


 *)
  open Slice

  (* 各々のスライシングを呼び出す *)
  let top n =
    if n = 1 then ExprSlicing1.top
    else if n = 2 then ExprSlicing2.top
    else if n = 3 then ExprSlicing3.top
    else raise Not_found

  let make expr item_cxt env cxt n =
    let slice' = 
      top n expr item_cxt env cxt
      |> Meta.clean "all" in
    set slice' (Times.cnt ()) (Times.time ())

  let write filename str =
    let file = open_out (filename ^ ".txt") in
    output_string file (str ^ "\n");
    close_out file

  let getLine expr item_cxt env cxt =

    let original =
      Pprintast.string_of_expression expr
      |> String.split_on_char '\n'
      |> String.concat "<br>" in
    Format.fprintf ppf "@[  original: %s@]@." original;

    let slices = List.map (make expr item_cxt env cxt) [1; 2; 3] in

    List.fold_left (
      fun d t ->
      String.concat
        "	"
        [d;
         Pprintast.string_of_expression (slice t);
         string_of_int (cnt t);
         string_of_float (time t)]) original slices
    |> write "result";

    slice (List.hd slices)

(*
  (* スライス（省略可能）、型推論の所要時間リスト *)
  type slice = {expr : expression option; times : float list}




  (* 各々のスライシングを呼び出す *)
  let top n =
    if n = 1 then ExprSlicing1.top
    else if n = 2 then ExprSlicing2.top
    else if n = 3 then ExprSlicing3.top
    else raise Not_found

  (* slice を新たに生成 *)
  let make_slice expr' n expr item_cxt env cxt =
    let slice' = 
      top n expr item_cxt env cxt
      |> Meta.clean "all" in
    {expr =
       if expr' = slice' && expr' <> skeleton' then
         None
       else
         Some slice';
     times = !times}

  let rec make_slices expr' n expr item_cxt env cxt =
    try
      let slice =
        make_slice expr' n expr item_cxt env cxt in
      slice ::
        make_slices (
            match slice.expr with
              Some slice' when n = 1 -> slice'
            | _ -> expr') (n + 1) expr item_cxt env cxt
    with _ -> []

  (* 書き込み *)
  let write filename str =
    let file = open_out (filename ^ ".txt") in
    output_string file (str ^ "\n");
    close_out file

  (* 全部まとめてよりも、スライス単位でファイルを作ってあとで結合するほうが良いかもしれない *)
  (* => 両方のバージョンを用意する *)

  (* original / slice1 / sum1 / time1 / slice2 / ... *)

  (* (n).txt : original / slice(n) / sum(n) / time(n) *)

  let getLine expr item_cxt env cxt =

    (* 各種スライス結果を求めて出力する *)
    let slices =
      make_slices skeleton' 1 expr item_cxt env cxt in

    let original =
      Pprintast.string_of_expression expr
      |> String.split_on_char '\n'
      |> String.concat "<br>" in

    Format.fprintf ppf "@[  original: %s@]@." original;

    match slices with
    | {expr = Some slice} :: _ ->
       List.fold_left (
           fun d {expr; times} ->
           let e = match expr with
               Some slice' -> Pprintast.string_of_expression slice'
             | None -> ""
           and s = string_of_int (List.length times)
           and t = string_of_float (List.fold_left (+.) 0. times) in
           (* 区切り文字 TAB *)
           String.concat "	" [d; e; s; t]
         ) original slices
       |> write "result";
       slice

    | _ -> assert false (* ここには到達しないはず *)
 *)
end


module Expression_slicing : sig
  (* Expression のスライシング *)
  val get :
    (expression * expr_cxt) * item_cxt -> Env.t -> expr_context
    -> expression

end = struct

  let print_slice = false

  let dummy_apply expr es =
    if List.for_all (fun e -> e = hole_of_exp e) es then []
    else
      [{expr with
         pexp_desc =
           Pexp_apply (hole_of_exp expr, List.map (fun e -> (Nolabel, e)) es)}]

  and abst_children expr es e =
    if e = hole_of_exp e then es
    else
      Desc.map_exp
        (fun e' -> if e = e' then hole_of_exp e else e')
        expr :: es

  (* dummy apply の追加 *)
  let abst_one' expr =
    Desc.fold_exp
      (abst_children expr)
      (match expr.pexp_desc with
       | Pexp_tuple es -> dummy_apply expr es
       | Pexp_array es -> dummy_apply expr es
       | _ -> []) expr

  (* construct だけ別処理 *)
  let abst_one expr = match expr.pexp_desc with
    | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as e)) ->
       List.map
         (fun e' -> {expr with pexp_desc = Pexp_construct (lid, Some e')})
         (List.fold_left (abst_children e) [] es)
       @ dummy_apply expr es
    | _ -> abst_one' expr

  let rec search (slices, exp_cxt, item_cxt, f) env cxt = match slices with
    | [] ->
       let ret = f () in
       if print_slice then
         begin
           Format.fprintf ppf "@[~search~@]@.";
           Format.fprintf ppf "@[  return: %a@]@."print_deb_exp ret
         end;
       ret
    | first :: rest ->
       (* 部分的に抽象化した結果、エラーになるかどうかをチェック *)
       let structure = item_cxt exp_cxt first in
       try
         if print_slice then
           begin
             Format.fprintf ppf "@[~search~@]@.";
             List.iter (
                 fun a ->
                 if a <> hole_of_exp a
                 then Format.fprintf ppf "@[  %a@]@." 
                                     print_deb_exp a
               ) (List.rev rest)
           end;
         (* Warnings.parse_options false "-A"; *)
         ignore (
             Typemod.type_structure env structure Location.none
           );
         (* Warnings.parse_options false Warnings.defaults_w; *)
         (* welltyped *)
         if print_slice && first <> hole_of_exp first then
           (Format.fprintf ppf "@[  welltyped : %a@]@."
                           print_deb_exp (exp_cxt first));
         search (rest, exp_cxt, item_cxt, f) env cxt
       with
         Typetexp.Error _
       | Typecore.Error _ ->
          (* illtyped *)
          (* Warnings.parse_options false Warnings.defaults_w; *)
          if print_slice
          then (Format.fprintf ppf "@[  illtyped : %a@]@."
                               print_deb_exp (exp_cxt first));
          get ((first, exp_cxt), item_cxt) env cxt
              
  (* get *)
  and get ((slice, exp_cxt), item_cxt) env pat_cxt =
    
    (* 与えた fd 等から desc_to_exp *)
    let slice' ?(e = slice) ?(s_all = skeleton') acc fd =
      Desc.to_exp fd acc s_all e in
    (* exp_cxt に desc から作った式を与える *)
    let exp_cxt' fd acc s_all = exp_cxt (slice' ~s_all acc fd) in
    (* slice * exp_cxt と pat_cxt を与えて get' する *)
    let sn' ?(c = pat_cxt) x = get' (x, item_cxt) env c in

    let e_in_v v = v.pvb_expr in
    let e_in_c c = c.pc_rhs in
    let e_in_l l = snd l in

    let f1_cxt acc_x fd e x rest acc y =
      exp_cxt' fd (acc @ [acc_x x y] @ rest) e in
(*
    let f1_v acc_x fd e v rest acc =
      (e_in_v v, f1_cxt acc_x fd e v rest acc) in
    let f1_l acc_x fd e l rest acc =
      (e_in_l l, f1_cxt acc_x fd e l rest acc) in
    let f1_c acc_x fd e c rest acc =
      (e_in_c c, f1_cxt acc_x fd e c rest acc) in
    let f1_e acc_x fd e s rest acc =
      (s, f1_cxt acc_x fd e s rest acc) in
    let no_f1 _ _ e _ _ _ = (e, id) in
 *)
    let no_fp acc _ s_all fd = slice' ~s_all acc fd in
    let rec fp lst acc s_all fd = match lst with
      | [] ->
         if print_slice && !on_pat_slice then
           Format.fprintf ppf "@[~finish get_slice_pat~@]@.";
         slice' ~s_all acc fd
      | c :: rest ->
         let ({pc_lhs = p'} as c') =
           try
             Map.c2 (fun _ e -> e)
                    (fun p e -> get_slice_pat p e pat_cxt env []) c
           with Pat_slice_error -> c in
         let emp_pat = Map.c1 id dummy_any c' in
         if try_empty_pat p' (slice' ~s_all (acc @ [emp_pat] @ rest) fd) exp_cxt env
         then fp rest (acc @ [emp_pat]) s_all fd
         else fp rest (acc @ [c']) s_all fd in

    let rec fp_v lst acc s_all fd = match lst with
      | [] ->
         if print_slice && !on_pat_slice then
           Format.fprintf ppf "@[~finish get_slice_pat~@]@.";
         slice' ~s_all acc fd
      | v :: rest ->
         let ({pvb_pat = p'} as v') =
           try
             Map.v1
               id (fun p -> get_slice_pat p s_all pat_cxt env []) v
           with Pat_slice_error -> v in
         let emp_pat = Map.v1 id dummy_any v' in
         if try_empty_pat p' (slice' ~s_all (acc @ [emp_pat] @ rest) fd) exp_cxt env
         then fp_v rest (acc @ [emp_pat]) s_all fd
         else fp_v rest (acc @ [v']) s_all fd in

    (* search に渡す *)
    let make_thunk ?(e = skeleton') xs x1 fx ?(fp = no_fp) fd =

      (* s_all : 全てのリストの処理が終わった後の仕上げで必要な関数 *)
      (* s_one : 着目している式での処理を行う関数 *)
      (* fd : acc と s_all を与えると desc が求まる関数 *)
      (* 各構文での処理中では、上の順番で定義する *)
      let acc_x x = Map.set_exp x1 x in
      let rec get_slice xs acc = match xs with
        | [] ->
           let s_all = sn' (e, exp_cxt' fd acc) in
           Size.set_all (if !on_pat_slice then fp
                         else no_fp ) fd fx acc s_all
        | first :: rest ->
           let s_one = sn' (fx first, f1_cxt acc_x fd e first rest acc) in
           get_slice rest (acc @ [acc_x first s_one]) in

      (* return で呼び出される部分 *)
      get_slice xs [] in


    (* サンクの定義 *)
    let f () = match slice.pexp_desc with

      | Pexp_let (flg, vs, e) ->
         (* let文 *)
         let fp = if flg = Recursive then no_fp else fp_v in
         make_thunk ~e vs Map.v1 e_in_v ~fp (Desc.e_let flg)
(*
         let fd acc s_all = Pexp_let (flg, acc, s_all) in
         let f1 = f1_v in
         let fp = if flg = Recursive then no_fp else fp_v in
         make_thunk ~e vs acc_v ~fp f1 fd pat_cxt
 *)

      | Pexp_apply (e, les) ->
         (* 関数適用 *)
         make_thunk ~e les Map.le e_in_l Desc.e_apply
(*
         let fd acc s_all = Pexp_apply (s_all, acc) in
         let f1 = f1_l in
         make_thunk ~e les acc_l f1 fd pat_cxt
 *)
      | Pexp_match (e, cs) ->
         (* match 文 *)
         make_thunk ~e cs Map.c1 ~fp e_in_c Desc.e_match
(*
         let fd acc s_all = Pexp_match (s_all, acc) in
         let f1 = f1_c in
         make_thunk ~e cs acc_c ~fp f1 fd pat_cxt
 *)
      | Pexp_try (e, cs) ->
         (* try 文 *)
         make_thunk ~e cs Map.c1 ~fp e_in_c Desc.e_try
(*
         let fd acc s_all = Pexp_try (s_all, acc) in
         let f1 = f1_c in
         make_thunk ~e cs acc_c ~fp f1 fd pat_cxt
 *)
      | Pexp_function cs ->
         (* function *)
         make_thunk cs Map.c1 ~fp e_in_c Desc.e_function
(*
         let fd acc _ = Pexp_function acc in
         let f1 = f1_c in
         make_thunk cs acc_c ~fp f1 fd pat_cxt
 *)
      | Pexp_fun (l, None, p, e) ->
         (* 関数抽象 *)
         (* fun P -> E *)
         let fd ?(pat = p) _ s_all = Pexp_fun (l, None, pat, s_all) in
         let c = plug_cxt pat_cxt (Lambda (p, Empty)) in
         let s_all = sn' ~c (e, exp_cxt' fd []) in
         let n = 1 + Size.get_one s_all in
         Size.set_one
           ~n
           (if not !on_pat_slice then slice' ~s_all [] fd
            else
              let pat = try (get_slice_pat p s_all pat_cxt env [])
                        with Pat_slice_error -> p in
              let s' = slice' ~s_all [] (fd ~pat) in
              let pat_empty_slice =
                slice' ~s_all [] (fd ~pat:(hole_of_pat pat)) in

            if try_empty_pat pat pat_empty_slice exp_cxt env
            then pat_empty_slice else s')

      | Pexp_tuple (es) ->
         (* 関数適用 *)
         make_thunk es Map.e1 id Desc.e_tuple
(*
         let fd acc _ = Pexp_tuple (acc) in
         let f1 = f1_e in
         make_thunk es acc_e f1 fd pat_cxt
 *)
      | Pexp_construct (lid, Some (e)) ->
         (* コンストラクタ *)
         (* 引数がある場合について考える *)
         let (es', e') = match e.pexp_desc with
             Pexp_tuple es -> (es, skeleton')
           | _ -> ([], e) in
         let fd acc s_all =
           Desc.e_construct lid [] (if es' = []
                                    then s_all
                                    else slice' ~e acc Desc.e_tuple) in

         make_thunk ~e:e' es' Map.e1 id fd

      | Pexp_record (les, eop) ->
         (* レコード *)
         let e = match eop with None -> skeleton' | Some e -> e in
         make_thunk ~e les Map.le e_in_l Desc.e_record
(*
         let fd acc _ = Pexp_record (acc, eop) in
         let f1 = f1_l in
         make_thunk les acc_l f1 fd pat_cxt
 *)
      | Pexp_array (es) ->
         (* 配列 *)
         make_thunk es Map.e1 id Desc.e_array
(*
         let fd acc _ = Pexp_array (acc) in
         let f1 = f1_e in
         make_thunk es acc_e f1 fd pat_cxt
 *)
      | Pexp_ifthenelse (e1, e2, eop) ->
         (* ifthenelse *)
         let fd ?(s1 = e1) ?(s2 = e2) ?(s3 = skeleton') _ _ =
           Desc.e_ifthenelse
             s1 s2 (if s3 = skeleton' then eop else Some s3) in
(*
           Pexp_ifthenelse (s1, s2, if s3 = skeleton' then eop else Some s3) in
 *)
         let exp_cxt'' fd' = exp_cxt' fd' [] skeleton' in
         let e1_cxt' s1 = exp_cxt'' (fd ~s1) in
         let s1 = sn' (e1, e1_cxt') in
         let e2_cxt' s2 = exp_cxt'' (fd ~s1 ~s2) in
         let s2 = sn' (e2, e2_cxt') in
         let e3_cxt' s3 = exp_cxt'' (fd ~s1 ~s2 ~s3) in
         let s3 = match eop with
           | None -> skeleton'
           | Some (e3) -> sn' (e3, e3_cxt') in

         (* if文のサイズは、各式のサイズから求める *)
         let n =
           1 + Size.get_one s1 + Size.get_one s2 + Size.get_one s3 in
         Size.set_one ~n (slice' [] (fd ~s1 ~s2 ~s3))

      | Pexp_constraint (e, ct) ->
         (* (E : core_type) *)
         make_thunk ~e [] Map.e1 id (Desc.e_constraint ct)

      | Pexp_sequence (e1, e2) ->
         (* 配列 *)
         let fd ?(s1 = e1) ?(s2 = e2) _ _ =
           Desc.e_sequence s1 s2 in
         let exp_cxt'' fd' = exp_cxt' fd' [] skeleton' in
         let e1_cxt' s1 = exp_cxt'' (fd ~s1) in
         let s1 = sn' (e1, e1_cxt') in
         let e2_cxt' s2 = exp_cxt'' (fd ~s1 ~s2) in
         let s2 = sn' (e2, e2_cxt') in
         let n =
           1 + Size.get_one s1 + Size.get_one s2 in
         Size.set_one ~n (slice' [] (fd ~s1 ~s2))

      | _ -> Size.set_one slice in (* その他構文は全て size 1 として扱う *)

    if print_slice then
      begin
        print_newline ();
        Format.fprintf
          ppf "@[~ get ~@]@.";
        Format.fprintf
          ppf "@[  target : %a@]@."
          print_deb_exp slice
      end;
    (* search を呼び出す *)

    search (abst_one slice, exp_cxt, item_cxt, f) env pat_cxt

  (* get' *)
  and get' ((slice, exp_cxt), item_cxt) env pat_cxt =
    if slice = hole_of_exp slice then Size.set_one slice (* □ は size 1 *)
    else get ((slice, exp_cxt), item_cxt) env pat_cxt

end

module Expression_slicingWithResize = struct

  let print_slice = false

  let wrap_expr expr_cxt expr_cxt' expr' =
    expr_cxt (expr_cxt' expr')
  let wrap_item item_cxt expr_cxt expr_cxt' expr' =
    item_cxt (wrap_expr expr_cxt expr_cxt') expr'
(*
  let reset_expr expr_cxt expr =
    expr |> Size.reset |> expr_cxt |> Size.reset
  let term_expr expr_cxt expr =
    if Size.set_resize then reset_expr expr_cxt expr
    else expr |> Size.terminated |> expr_cxt |> Size.terminated
 *)
  let dummy_apply es expr =
    let les = List.map (fun e -> (Nolabel, e)) es in
    let e = Abst.exp expr in
    Desc.to_exp Desc.e_apply les e expr

  let replace e1 e2 =
    if e2.pexp_loc = e1.pexp_loc then e1
    else if e2.pexp_loc = Location.none then
      {e1 with pexp_desc = e2.pexp_desc}
    else e2

  let return kind1 kind2 expr =
    if print_slice then
        begin
          print_newline ();
          Format.fprintf
            ppf "@[~ %s ~@]@."
            kind1;
          Format.fprintf
            ppf "@[%s : %a@]@."
            kind2
            print_deb_exp expr;
        end;
    expr

  let rec search ((child, sel, expr_cxt, slice_cxt), item_cxt) env =

    let g pair =
      get (pair, item_cxt) env in
    let f sel' slice =
      slice_cxt sel expr_cxt (if sel' then Size.reset slice else slice)
    and f' sel' =
      slice_cxt sel' id child
    and is1 = Size.is1 child in
    try
      if print_slice then
        begin
          print_newline ();
          Format.fprintf
            ppf "@[~ search ~@]@.";
          Format.fprintf
            ppf "@[%s : %a@]@."
            (if sel then "expect" else "one")
            print_deb_exp (f false child);
        end;
      let structure = item_cxt (f false) child in
      ignore (Typemod.type_structure env structure Location.none);
      assert sel;
      search ((child, false, expr_cxt, slice_cxt), item_cxt) env

      with
      | Typecore.Error _ ->
         (* illtyped *)
         if print_slice then
           Format.fprintf
             ppf "@[illtyped (%s).@]@."
             (if is1 then "is 1" else if sel then "expect" else "one");

         if sel && is1 then
           g (f true child, id)
         else if sel then
           g (child, f false)
         else
           let slice = f' false in
           if Size.fltr0 slice then g (slice, expr_cxt)
           else g (expr_cxt slice, id)

      | _ ->
         (* welltyped *)
         if print_slice then
           Format.fprintf
             ppf "@[welltyped (%s).@]@."
             (if is1 then "is 1" else "greater 1");
         if f' true = f' false && is1 then
           g (Size.reset child, expr_cxt)
         else
           let f'' = f true in
           if is1 then
             g (f'' child, id)
           else
             g (child, f'')

  and get ((expr, expr_cxt), item_cxt) env =

    if print_slice then (
      print_newline ();
      Format.fprintf
        ppf "@[~ get ~@]@.";
      Format.fprintf
        ppf "@[expr : %a@]@."
          Pprintast.expression expr;
    );

    if Size.fltr0 expr then
      let (child, expr_cxt_one, expr_cxt_expect) = Size.get_child expr in
      let sel =
        if print_slice then
          Format.fprintf
            ppf "@[child : %a@]@."
            print_deb_exp child;
        Size.fltr1 child in
      let slice_cxt sel f slice =
        let f' = if sel then expr_cxt_expect else expr_cxt_one in
        f (f' slice) in
      search ((child, sel, expr_cxt, slice_cxt), item_cxt) env
    else
      return "get" "return" (expr_cxt expr)


  and top' env cxt item_cxt expr =

    if Desc.leaf_exp expr then
      (* leaf には何もしない *)
      expr
    else
      (* fold 関数 *)
      let fold slice =
        Desc.fold_exp (
            fun slice' e' ->
            if Size.fltr0 e' then
              (* e' が 未確定の場合 *)
              let expr_cxt e = Desc.map_exp (replace e) slice' in
              top' env cxt (wrap_item item_cxt expr_cxt) e' |> expr_cxt
            else
              (* e' が確定している場合は何もしない *)
              slice'
        ) slice slice |> Size.resize in

      (* 特定の構文には専用の処理を施す *)
      match expr.pexp_desc with

      | Pexp_let (flg, vs, e) ->
         (* Let *)
         let expr_cxt e' =
           {expr with pexp_desc = Pexp_let (flg, vs, e')} in
         let cxt' = Let (flg, vs, cxt) in
         top ((e, replace expr), wrap_item item_cxt expr_cxt) env cxt'

      | Pexp_fun (l, eop, p, e) ->
         (* Lambda *)
         let expr_cxt e' =
           {expr with pexp_desc = Pexp_fun (l, eop, p, e')} in
         let cxt' = Lambda (p, cxt) in
         top ((e, replace expr), wrap_item item_cxt expr_cxt) env cxt'

      | Pexp_tuple es ->
         (* tuple *)
         top2 ((expr, (fold, Desc.map_exp Abst.exp, es)), item_cxt) env cxt

      | Pexp_construct (lid, Some e) ->
         let map = Desc.map_exp Abst.exp in
         let expr_cxt_set = match e.pexp_desc with
           | Pexp_tuple es ->
              let rec map' e' =
                if e' = expr then
                  map' (map e)
                else
                  {expr with pexp_desc = Pexp_construct (lid, Some e')} in
              let rec fold' es' expr' = match es' with
                | [] ->
                   if expr = expr' then
                     fold' es e
                   else return "top" "construct" (map' expr' |> Size.reset)
                | first :: rest ->
                   let expr_cxt e' =
                     Desc.map_exp (replace e') expr' in
                   top ((first, id),
                        wrap_item item_cxt (wrap_expr map' expr_cxt)) env cxt
                   |> expr_cxt |> fold' rest in
              (fold' [], map', es)
           | _ ->
              (fold, map, [e]) in
         top2 ((expr, expr_cxt_set), item_cxt) env cxt

      | Pexp_array es ->
         (* array *)
         top2 ((expr, (fold, Desc.map_exp Abst.exp, es)), item_cxt) env cxt

      | Pexp_ifthenelse (e1, e2, eop) ->
         (* if文 *)
         (* 型を決定する部分式は e2 と eop *)
         let f sel1 sel2 e =
           let e1' = if sel1 then Abst.exp e1 else e1
           and e2' = if sel2 then Abst.exp e2 else e2
           and eop' = match eop with
             | Some e3 when e = e3 -> Some (Abst.exp e3)
             | _ -> eop in
           {expr with pexp_desc = Pexp_ifthenelse (e1', e2', eop')} in
         let error sel1 sel2 e =
           try
             let structure = item_cxt (f sel1 sel2) e in
             ignore (Typemod.type_structure env structure Location.none);
             false
           with
             _ -> true in
         let sel1 = error true false skeleton' in
         let (sel2, e3') =
           let ret sel = match eop with
             | Some e3 when (not sel) -> error sel1 false e3
             | _ -> error sel1 true skeleton' in
           match eop with
           | None -> (ret false, skeleton')
           | Some e3 ->
              let sel = Size.get 0 e2 > Size.get 0 e3 in
              ret sel
              |> (fun sel' ->
                   (if sel || sel' then sel = sel' else ret true),
                   (if sel' = sel then skeleton'
                    else if ret false || sel' then e3 else skeleton')) in
         f sel1 sel2 e3' |> fold

      | _ -> fold expr

  and top1 ((expr, expr_cxt), item_cxt) env =
    try

      let structure = item_cxt expr_cxt expr in
      ignore (Typemod.type_structure env structure Location.none);
      assert (Size.is1 expr);

      Size.reset expr |> return "top1" "need"

    with
    | Typecore.Error _ ->
       return "top1" "ignore" expr |> expr_cxt

    | _ ->
       top ((expr, id), item_cxt) env Empty

  and top2 ((expr, (fold, map, es)), item_cxt) env cxt =

    let error expr_cxt =
      try
        ignore (
            Typemod.type_structure
              env (item_cxt expr_cxt expr) Location.none);
        false
      with _ -> true in

(*
    let sel1 = error (dummy_apply es) && es <> []
    and sel2 = error map in

    if sel1 && sel2 then
 *)

    if error (dummy_apply es) && es <> [] then
      (fun e -> Pprintast.expression ppf e; e) (dummy_apply es expr)
      |> top' env cxt item_cxt
    else if error map then
      map expr |> Size.reset |> return "top2" "abst all"
    else fold expr

  and top ((expr, expr_cxt), item_cxt) env cxt = match cxt with   

    | Let (flg, vs, _) ->
       (* let *)
       let e = top ((expr, id), item_cxt) env Empty in
       let let_cxt vs' = Exp.let_ flg vs' e in
       List.fold_left (
           fun vs' {pvb_expr = en} ->
           let set_vs en' =
             List.map (Map.v1 (replace en') id) vs' in
           let expr_cxt' en' = let_cxt (set_vs en') in
           top1 ((en, Abst.exp), wrap_item item_cxt expr_cxt') env
           |> set_vs
         ) vs vs |> let_cxt
       |> expr_cxt
       |> Size.reset
       |> return "top" "let"

    | Lambda (p, _) ->
       let e = top ((expr, id), item_cxt) env Empty in
       Exp.fun_ Nolabel None p e
       |> expr_cxt
       |> Size.reset
       |> return "top" "lambda"

    | _ ->
       (* スライシングの開始 *)
       (* モジュールの外から呼ばれる関数 *)
       if true then
         let slice = top' env cxt item_cxt expr in
         if Size.fltr0 slice then
           get ((slice, id), item_cxt) env
         else
           slice
       else
         get ((expr, id), item_cxt) env


end

module Expression_slicing' = struct

  let print_slice = false

  (* expression の size を更新する場合を、切り替えられるようにするor追加する *)
  (* ↑terminated になった子ノードは親のサイズに含まない *)

  (* if文の構文チェック *)
  let check_es = true

  let wrap_expr expr_cxt expr_cxt' expr' =
    expr_cxt (expr_cxt' expr')
  let wrap_item item_cxt expr_cxt expr_cxt' expr' =
    item_cxt (wrap_expr expr_cxt expr_cxt') expr'
(*
  let reset_expr expr_cxt expr =
    expr |> Size.reset |> expr_cxt |> Size.reset
  let term_expr expr_cxt expr =
    if Size.set_resize then reset_expr expr_cxt expr
    else expr |> Size.terminated |> expr_cxt |> Size.terminated
 *)
  let dummy_apply es expr =
    let les = List.map (fun e -> (Nolabel, e)) es in
    let e = Abst.exp expr in
    Desc.to_exp Desc.e_apply les e expr

  let replace e1 e2 =
    if e2.pexp_loc = e1.pexp_loc then e1 else e2
  let typed_cxt slice_cxt expr_cxt child =
    slice_cxt false expr_cxt (Size.terminated child)

  let return kind1 kind2 expr =
    if print_slice then
        begin
          print_newline ();
          Format.fprintf
            ppf "@[~ %s ~@]@."
            kind1;
          Format.fprintf
            ppf "@[%s : %a@]@."
            kind2
            print_deb_exp expr;
        end;
    expr

  let rec search ((child, sel, expr_cxt, slice_cxt), item_cxt) env cxt =

    let expr_cxt' = slice_cxt sel expr_cxt
    and is1 = Size.is1 child in
    let g (expr', expr_cxt') = get ((expr', expr_cxt'), item_cxt) env cxt in

    try

      if print_slice then
        Format.fprintf
          ppf "@[%s: %a@]@."
          (if sel then "expect" else "one")
          print_deb_exp (expr_cxt' child);
      let structure = item_cxt expr_cxt' child in
      ignore (Typemod.type_structure env structure Location.none);

      assert sel;
      search ((child, false, expr_cxt, slice_cxt), item_cxt) env cxt

      with
      | Typecore.Error _ ->
         (* illtyped *)
         if print_slice then
           Format.fprintf
             ppf "@[illtyped (%s).@]@."
             (if is1 then "is 1" else if sel then "expect" else "one");

         if sel && is1 then
           g (expr_cxt' (Size.terminated child), id)
         else if sel then
           g (child, expr_cxt')
         else
           g (slice_cxt sel id child, expr_cxt)

      | _ ->
         (* welltyped *)
         if print_slice then
           Format.fprintf
             ppf "@[welltyped (%s).@]@."
             (if is1 then "is 1" else "greater 1");
         if is1 then
           g (typed_cxt slice_cxt id child, expr_cxt)
         else
           let slice = g (child, typed_cxt slice_cxt expr_cxt) in
           g (slice, id)

  and get ((expr, expr_cxt), item_cxt) env cxt =

    let (expr', expr_cxt_expect, expr_cxt_one) = Size.getChild3 expr in
    if print_slice then
      begin
        print_newline ();
        Format.fprintf
          ppf "@[~ get ~@]@.";
        Format.fprintf
          ppf "@[expr : %a@]@."
          print_deb_exp expr;
        Format.fprintf
          ppf "@[child : %a@]@."
          print_deb_exp expr';
      end;

    if Desc.fold_exp (* 子ノードがある式の場合：未確定のノードがあるかどうか *)
         (fun b e -> b || Size.fltr0 e)
         (Desc.fold_exp (* 子ノードがない式の場合：expr' が未確定かどうか *)
            (fun _ _ -> false)
            (Size.fltr0 expr' && expr = expr') expr') expr then
      begin
        let slice_cxt sel f slice =
          f (slice |> if sel then expr_cxt_expect else expr_cxt_one) in
        search (
            (expr', Size.fltr1 expr', expr_cxt, slice_cxt),
            item_cxt) env cxt
      end
    else
      get' ((expr, expr_cxt), item_cxt) env cxt




(*
  let rec top'' (fold, map, sel) env cxt item_cxt expr =
    try
      let structure = item_cxt (map sel) expr in
      ignore (Typemod.type_structure env structure Location.none);
      assert sel;
      top'' (fold, map, false) env cxt item_cxt expr
    with
    | Typecore.Error _ ->
       let expr' = map sel expr |> Size.resize in
       (* illtyped *)
       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~ top ~@]@.";
           Format.fprintf
             ppf "@[%s : %a@]@."
             (if sel then "abst all" else "dummy apply")
             print_deb_exp expr'
         end;
       if sel then
         top' env cxt item_cxt expr'
(*
         top' env cxt item_cxt expr'
 *)
       else
         top' env cxt item_cxt expr'
              
(*
         top' env cxt item_cxt expr'
 *)
    | _ ->
       (* welltyped *)
       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~ top ~@]@.";
           Format.fprintf
             ppf "@[no need dummy : %a@]@."
             print_deb_exp expr
         end;
       fold expr

  and top' env cxt item_cxt expr =

    let expr_cxt expr'= Desc.map_exp (replace expr') expr in
    let item_cxt' = wrap_item item_cxt expr_cxt in
    let t fop e cxt' =
      match fop with
      | None -> top e item_cxt' env cxt'
      | Some item_cxt'' -> top e item_cxt'' env cxt' in

    (* fold 関数 *)
    (* 深さ優先で子ノードをチェック *)
    let fold slice =
      Desc.fold_exp (
          fun slice' e' ->
          if Size.fltr0 e' then
            (* e' が 未確定の場合 *)
            let expr_cxt e = Desc.map_exp (replace e) slice' in
            top' env cxt (wrap_item item_cxt expr_cxt) e' |> expr_cxt
          else
            (* e' が確定している場合は何もしない *)
            slice'
        ) slice slice |> Size.resize in

(*
    let f () =
      Desc.fold_exp (
          fun expr' e ->
          if Size.fltr0 e then
            let expr_cxt' e' = Desc.map_exp (replace e') expr' in
            let item_cxt'' =
              wrap_item item_cxt expr_cxt' in
            top' env cxt item_cxt'' e |> expr_cxt'
          else
            expr'
        ) expr expr in
 *)


    if Desc.leaf_exp expr then expr
    else
      match expr.pexp_desc with
      | Pexp_let (flg, vs, e) ->
         (* Let *)
         (* in 以下のスライスを先に求める *)
         (* value binding list を差し替える関数 *)
         let e' = Let (flg, vs, cxt) |> t None e in
         let vs_cxt vs' = Desc.to_exp (Desc.e_let flg) vs' e' expr in

         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~ top ~@]@.";
             Format.fprintf
               ppf "@[let : %a@]@."
               print_deb_exp (vs_cxt vs)
           end;

         (* value binding list のスライスを求める *)
         let slice =
           List.fold_left (
               fun vs' {pvb_expr = en} ->
               let set_vs en' =
                 List.map (
                     fun vn ->
                     Map.v1 (fun e' -> if en = e' then en' else e') id
                            (* パターンのスライスを入れる場合は、idを変更する *) vn
                   ) vs' in
               let expr_cxt_let en' = vs_cxt (set_vs en') in
               let item_cxt_let = wrap_item item_cxt expr_cxt_let in
               t (Some item_cxt_let) en cxt |> set_vs
             ) vs vs |> vs_cxt |> (if Size.set_resize then Size.reset else Size.terminated) in
         
         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~ top (return) ~@]@.";
             Format.fprintf
               ppf "@[let : %a@]@."
               print_deb_exp slice
           end;
         slice
           
      | Pexp_fun (_, _, p, e) ->
         (* Lambda *)
         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~ top ~@]@.";
             Format.fprintf
               ppf "@[lambda : %a@]@."
               print_deb_exp expr
           end;
         let slice =
           Lambda (p, cxt) |> t None e |> term_expr expr_cxt
           |> Desc.map_exp_all Size.reset in
         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~ top (return) ~@]@.";
             Format.fprintf
               ppf "@[lambda : %a@]@."
               print_deb_exp slice
           end;
         slice
           
      | Pexp_tuple es when check_dummy ->
         let sel' = List.for_all Size.fltr0 es in
         let map sel =
           if sel then Desc.map_exp Abst.exp
           else if sel' then dummy_apply es else hole_of_exp in
         top'' (fold, map, sel') env cxt item_cxt expr

      | Pexp_array es when check_dummy ->
         let sel' = List.for_all Size.fltr0 es in
         let map sel =
           if sel then Desc.map_exp Abst.exp
           else if sel' then dummy_apply es else hole_of_exp in
         top'' (fold, map, sel') env cxt item_cxt expr

      | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as e))
           when check_all ->
         (* dummy apply check *)
         let expr_cxt' ?(expr' = expr) e' =
           {expr' with pexp_desc = Pexp_construct (lid, Some e')} in

         let map sel slice =
           if sel then
             (* abst all *)
             expr_cxt' (Desc.map_exp Abst.exp slice)
           else
             (* dummy apply *)
             dummy_apply es expr in

         let fold' slice =
           let item_cxt' = wrap_item item_cxt expr_cxt' in
           Desc.fold_exp (
             fun slice' e ->
             let expr_cxt'' e'' = Desc.map_exp (replace e'') slice' in
             t (Some (wrap_item item_cxt' expr_cxt'')) e cxt |> expr_cxt''
             ) slice slice |> expr_cxt' |> Size.resize in

(*
         let fold' slice =
           let expr_cxt'' ?(es'' = []) e'' =
             expr_cxt' {
                 slice with (* e'' に差し替える *)
                 pexp_desc =
                   Pexp_tuple (
                       if es'' = [] then
                         List.map (replace e'') es
                       else
                         es'')} in
           let es'' =
             List.fold_left (
                 fun acc e'' ->
                 acc @ [t (Some (wrap_item item_cxt expr_cxt'')) e'' cxt]
               ) [] es in
           expr_cxt'' ~es'' skeleton' |> Size.resize in
 *)
         
         top'' (fold', map, true) env cxt item_cxt e      
               
      (*
    | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as e)) when false ->
       (* dummy apply check *)
       let f' sel slice =
         if sel then
           (* abst all *)
           {slice with
             pexp_desc =
               Pexp_construct
                 (lid,
                  Some (
                      Desc.map_exp
                        (fun e ->
                          hole_of_exp e
                          |> if Size.set_resize then
                               Size.reset
                             else
                               Size.terminated) e))}
         else
           (* dummy apply *)
           dummy_apply es slice
       and f () =
         let item_cxt'' =
           wrap_item item_cxt' (fun e' -> Desc.map_exp (replace e') e) in
         Desc.map_exp (
             fun child -> t (Some item_cxt'') child cxt
           ) e |> term_expr expr_cxt in
       top'' (f, (f', true, expr)) env cxt item_cxt
 *)

      | Pexp_ifthenelse (e1, e2, eop) when check_ifthenelse ->
         (* if文 *)
         (* 型を決定する部分式は e2 と eop *)
         let f sel1 sel2 e =
           let e1' = if sel1 then Abst.exp e1 else e1
           and e2' = if sel2 then Abst.exp e2 else e2
           and eop' = match eop with
             | Some e3 when e = e3 -> Some (Abst.exp e3)
             | _ -> eop in
           {expr with pexp_desc = Pexp_ifthenelse (e1', e2', eop')} in
         let get_sel sel1 sel2 e =
           try
             let structure = item_cxt' (f sel1 sel2) e in
             ignore (Typemod.type_structure env structure Location.none);
             false
           with
             _ -> true in
         let sel1 = get_sel true false skeleton' in
         let (sel2, e3') =
           let ret sel = match eop with
             | Some e3 when (not sel) -> get_sel sel1 false e3
             | _ -> get_sel sel1 true skeleton' in
           match eop with
           | None -> (ret false, skeleton')
           | Some e3 ->
              let sel = Size.get 0 e2 > Size.get 0 e3 in
              ret sel
              |> (fun sel' ->
                   (if sel || sel' then sel = sel' else ret true),
                   (if sel' = sel then skeleton'
                    else if ret false || sel' then e3 else skeleton')) in
         f sel1 sel2 e3' |> fold
                              
      | _ -> fold expr
 *)

  and get' ((expr, expr_cxt), _) _ cxt = match cxt with
    | Let _ ->
       return "get" "return (let)" (expr_cxt expr)
    | Lambda _ ->
       return "get" "return (lambda)" (expr_cxt expr)
    | _ ->
       return "get" "return (empty)" (expr_cxt expr)



  let rec top'' (fold, map, es) env cxt item_cxt expr =

    let error expr_cxt =
      try
        ignore (
            Typemod.type_structure
              env (item_cxt expr_cxt expr) Location.none);
        false
      with _ -> true in

    if error (dummy_apply es) then
      let rec dummy_apply' es' = match es' with
          [] -> Abst.exp expr |> return "top" "ignore"
        | first :: rest ->
           if error (dummy_apply (Abst.exp first :: rest)) then
             dummy_apply' rest
           else
             let expr_cxt e =
               if e = skeleton' then
                 return "top" "dummy_apply (before)" expr
                 |> dummy_apply es
                 |> return "top" "dummy_apply (after)"
               else
                 dummy_apply [e] expr in
             ignore (expr_cxt skeleton');
             top' env cxt (wrap_item item_cxt expr_cxt) first
             |> expr_cxt |> Size.resize in
      dummy_apply' es
    else if error map then
      map expr |> Size.reset |> return "top" "abst all"
    else fold expr

  and top' env cxt item_cxt expr =

    if Desc.leaf_exp expr then
      (* leaf には何もしない *)
      expr
    else
      (* fold 関数 *)
      let fold slice =
        Desc.fold_exp (
            fun slice' e' ->
            if Size.fltr0 e' then
              (* e' が 未確定の場合 *)
              let expr_cxt e = Desc.map_exp (replace e) slice' in
              top' env cxt (wrap_item item_cxt expr_cxt) e' |> expr_cxt
            else
              (* e' が確定している場合は何もしない *)
              slice'
        ) slice slice |> Size.resize in

      (* 特定の構文には専用の処理を施す *)
      match expr.pexp_desc with

      | Pexp_let (flg, vs, e) ->
         (* let *)
         let cxt' = Let (flg, vs, cxt) in
         let let_cxt ?(vs' = vs) e' =
           {expr with pexp_desc = Pexp_let (flg, vs', e')} in
         let e' = top e (wrap_item item_cxt let_cxt) env cxt' in
         let let_cxt' vs' = let_cxt ~vs' e' in

         (* value binding list のスライスを求める *)
         List.fold_left (
             fun vs' {pvb_expr = en} ->
             let set_vs en' =
               List.map (
                   fun vn ->
                   Map.v1 (fun e'' -> if en = e'' then en' else e'') id vn
                 ) vs' in
             let expr_cxt en' = let_cxt' (set_vs en') in
             top en (wrap_item item_cxt expr_cxt) env cxt
             |> set_vs
           ) vs vs |> let_cxt'
         |> Size.reset
         |> return "top" "let"


      | Pexp_fun (l, eop, p, e) ->
         (* Lambda *)
         let cxt' = Lambda (p, cxt) in
         let lambda_cxt e' =
           {expr with pexp_desc = Pexp_fun (l, eop, p, e')} in
         top e (wrap_item item_cxt lambda_cxt) env cxt'
         |> lambda_cxt
         |> Size.reset
         |> return "top" "lambda"

      | Pexp_tuple es when check_es ->
         (* tuple *)
         top'' (fold, Desc.map_exp Abst.exp, es) env cxt item_cxt expr

      | Pexp_construct (lid, Some e) when check_es ->
         (* construct has element *)
         let es = match e.pexp_desc with
           | Pexp_tuple es' -> es' | _ -> [e] in
         let rec map e' =
           if e' = expr && es = [e] then
             map (Abst.exp e)
           else if e' = expr then
             map (Desc.map_exp Abst.exp e)
           else
             {expr with pexp_desc = Pexp_construct (lid, Some e')} in
         let rec fold' es' expr' =  match es' with
           | [] ->
              if expr = expr' && es = [e] then
                top e (wrap_item item_cxt map) env cxt
                |> map |> fold' []
              else if expr = expr' then
                fold' es e
              else return "top" "construct" (map expr' |> Size.reset)
           | first :: rest ->
              let expr_cxt e' =
                Desc.map_exp (replace e') expr' in
              top first
                  (wrap_item item_cxt (wrap_expr map expr_cxt)) env cxt
              |> expr_cxt |> fold' rest in
         top'' (fold' [], map, es) env cxt item_cxt expr

      | Pexp_array es when check_es ->
         (* array *)
         top'' (fold, Desc.map_exp Abst.exp, es) env cxt item_cxt expr

      | _ -> fold expr


  and top expr item_cxt env cxt =
    (* スライシングの開始 *)
    (* モジュールの外から呼ばれる関数 *)
    if Size.set_resize then
      Expression_slicingWithResize.top ((expr, id), item_cxt) env cxt
    else
      let slice = top' env cxt item_cxt expr in
      if Size.fltr0 slice then
        (* 特殊な構文を含まない *)
        get ((slice, id), item_cxt) env cxt
      else
        (* 特殊な構文を含む *)
        slice

end


module Expression_slicingNoResize = struct

  let print_slice = true

  (* expression の size を更新する場合を、切り替えられるようにするor追加する *)
  (* ↑terminated になった子ノードは親のサイズに含まない *)

  let wrap_expr expr_cxt expr_cxt' expr' =
    expr_cxt (expr_cxt' expr')
  let wrap_item item_cxt expr_cxt expr_cxt' expr' =
    item_cxt (wrap_expr expr_cxt expr_cxt') expr'
(*
  let reset_expr expr_cxt expr =
    expr |> Size.reset |> expr_cxt |> Size.reset
  let term_expr expr_cxt expr =
    if Size.set_resize then reset_expr expr_cxt expr
    else expr |> Size.terminated |> expr_cxt |> Size.terminated


 *)

  let dummy_apply es expr =
    let les = List.map (fun e -> (Nolabel, e)) es in
    let e = Abst.exp expr in
    Desc.to_exp Desc.e_apply les e expr

  let replace e1 e2 =
    if e2.pexp_loc = Location.none
    then Size.reset {e1 with pexp_desc = e2.pexp_desc}
    else if e2.pexp_loc = e1.pexp_loc then e1 else e2

  let return kind1 kind2 expr =
    if print_slice then
        begin
          print_newline ();
          Format.fprintf
            ppf "@[~ %s ~@]@."
            kind1;
          Format.fprintf
            ppf "@[%s : %a@]@."
            kind2
            print_deb_exp expr;
        end;
    expr

  let has_es expr =
    if Desc.leaf_exp expr then false
    else
      match expr.pexp_desc with
      | Pexp_tuple _ -> true
      | Pexp_array _ -> true
      | _ -> false

  let rec search ((child, sel, expr_cxt, slice_cxt), item_cxt) env cxt =

    let expr_cxt'' slice =
      slice_cxt false expr_cxt (Size.reset slice)
    and g (expr', expr_cxt') =
      get ((expr', expr_cxt'), item_cxt) env cxt
    and expr_cxt' = slice_cxt sel expr_cxt
    and greater1 = Size.fltr1 child in

    let expr = expr_cxt' child in
    try
      let structure = item_cxt expr_cxt' child in
      ignore (Typemod.type_structure env structure Location.none);
      assert sel;

      (* go abst one *)
      search ((child, false, expr_cxt, slice_cxt), item_cxt) env cxt

    with
    | Typecore.Error _ ->
       (* illtyped *)
       ignore (return (if sel then "search (one)" else "search (expect)")
                      "illtyped" expr);

       if has_es child && sel && greater1 then
         get' ((child, expr_cxt'), item_cxt) env cxt
       else if sel && greater1 then
         g (child, expr_cxt')
       else if sel then
         g (expr, id)
       else
         g (slice_cxt sel id child, expr_cxt)

    | _ ->
       (* welltyped *)
       let expr =
         let e = expr_cxt'' child in
         if e = hole_of_exp e then
           (slice_cxt true expr_cxt (Size.reset child)) else e in
       ignore (return (if greater1 then "search (greater1)" else "search (is1)")
                      "welltyped" expr);
       
       let slice =
         if greater1 then
           let g' env cxt =
             if has_es child then
               get' ((child, id), wrap_item item_cxt expr_cxt'') env cxt
             else
               get ((child, id), wrap_item item_cxt expr_cxt'') env cxt in
           g' env cxt |> expr_cxt''
         else
           expr in
       if Size.fltr0 slice then
         g (slice, id)
       else
         slice

  and search' ((child, sel, expr_cxt, slice_cxt), item_cxt) env cxt =
    
    let g (expr', expr_cxt') =
      get ((expr', id), wrap_item item_cxt expr_cxt') env cxt in

    try
      let structure = item_cxt (slice_cxt sel expr_cxt) child in
      ignore (Typemod.type_structure env structure Location.none);
      assert sel;
      search' ((child, false, expr_cxt, slice_cxt), item_cxt) env cxt

    with
    | Typecore.Error _ ->
       (* illtyped *)
       if Desc.leaf_exp child then
         return "leaf" "illtyped" (slice_cxt false expr_cxt child)
       else
         (* need get *)
         slice_cxt sel expr_cxt child |> return "node" "illtyped"
    | _ ->
       (* welltyped *)
       if Desc.leaf_exp child then
         return "leaf" "welltyped" (slice_cxt true expr_cxt child)
       else if child = skeleton' then
         g (child, expr_cxt) |> expr_cxt
       else
         g (return "node" "welltyped" (expr_cxt child), id)

  and get ((expr, expr_cxt), item_cxt) env cxt =

    let size = Size.get_one expr in

    if size < 1 then
      return "return" "Empty" (expr_cxt expr)

    else if size = 1 && not (Desc.leaf_exp expr) then
      get ((Size.reset expr, expr_cxt), item_cxt) env cxt


    else
      let g expr' =
        get ((expr', id), item_cxt) env cxt
      and g' ?(cxt' = cxt) expr' expr_cxt' =
        get' ((skeleton',
               fun slice -> if slice = skeleton' then expr' else slice),
              wrap_item item_cxt expr_cxt') env cxt' in

      match expr.pexp_desc with
      | Pexp_fun (l, eop, p, e) ->
         (* Lambda *)
         let lambda_cxt p' e' =
           wrap_expr expr_cxt (replace expr) (Exp.fun_ l eop p' e')
         and cxt' = Lambda (p, cxt) in
         let e' = g' ~cxt' e (lambda_cxt p) in
         lambda_cxt p e' |> return "return" "Lambda" |> g

      | Pexp_let (flg, vs, e) ->
         (* Let *)
         let let_cxt vs' e' =
           wrap_expr expr_cxt (replace expr) (Exp.let_ flg vs' e')
         and cxt' = Let (flg, vs, cxt) in
         let e' = g' ~cxt' e (let_cxt vs) in
         let vs' =
           List.fold_left (
               fun vs' {pvb_expr = en} ->
               (* value binding の expression を差し替える *)
               let set_vs en' =
                 List.map (Map.v1 (replace en') id) vs' in
               g' en (fun en' -> let_cxt (set_vs en') e')
               |> set_vs) vs vs in
         let_cxt vs' e' |> return "return" "Let" |> g


      | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as e)) ->

         (* construct *)
         let expr_cxt' e' =
           {expr with pexp_desc = Pexp_construct (lid, Some e')} in

         if List.fold_left Size.get 1 es = Size.get_one e then

           let child = return "get" "construct" (Size.reset1 (-) e) in
           let slice_cxt sel f slice =
             if sel then
               f slice |> dummy_apply es
             else
               Desc.map_exp Abst.exp slice |> f |> Size.reset in
           let slice =
             search' ((child, true,
                       expr_cxt', slice_cxt),
                      wrap_item item_cxt expr_cxt) env cxt in
           get ((slice, expr_cxt), item_cxt) env cxt
         else
           let set_es es' e' = List.map (replace e') es' in
           let const_cxt es' e' =
             expr_cxt' {e with pexp_desc = Pexp_tuple (set_es es' e')} in
           let es' =
             List.fold_left (
                 fun es' e' ->
                 get ((e', id), wrap_item item_cxt (const_cxt es')) env cxt
                 |> set_es es'
               ) es es in
           const_cxt es' skeleton' |> expr_cxt

      | _ ->
         (* Empty *)
         let (child, expr_cxt_expect, expr_cxt_one) =
           Size.getChild2 expr in
         let slice_cxt sel f slice =
           f (slice
              |> if sel then expr_cxt_expect else expr_cxt_one) in
         search ((return "get" "child" child,
                  child <> expr && Size.fltr1 child,
                  expr_cxt, slice_cxt), item_cxt) env cxt

  and get' ((expr, expr_cxt), item_cxt) env cxt = match expr.pexp_desc with

    | _ ->
       let es = Desc.fold_exp (fun es' e -> es' @ [e]) [] expr in
       let sel1 = List.for_all Size.fltr0 es
       and sel2 = expr = skeleton' in

       let child =
         if sel2 then
           return "get'" "ig" (expr_cxt expr)
         else if sel1 then
           return "get'" "es" (Size.reset1 (-) expr)
         else
           expr in
       
       if child = expr then
         get ((expr, expr_cxt), item_cxt) env cxt

       else
         let slice_cxt sel f slice =
           let (_, expr_cxt_expect, expr_cxt_one) =
             if sel1 then
               (expr,
                dummy_apply es,
                fun expr' -> Desc.map_exp Abst.exp expr' |> Size.reset)
             else
               Size.getChild3 expr in
           f (if sel then expr_cxt_expect slice
              else expr_cxt_one slice) in
         let slice =
           search' ((child, sel1, expr_cxt, slice_cxt), item_cxt) env cxt in
         if Size.fltr0 slice then
           get ((slice, id), item_cxt) env cxt
         else
           slice


end

module Expression_slicing'' = struct

  let print_slice = false

  (* 置き換え関数 *)

  let replace slice expr = desc_to_exp slice.pexp_desc expr

  let replace2 slice expr =
    Size.terminated (desc_to_exp slice.pexp_desc expr)

  (* 表示用 *)
  let skeleton2 = Exp.ident (mknoloc (Longident.parse "■"))
  let show_cxt sel slice =
    if slice = skeleton' then slice
    else (
      replace skeleton2 slice
      |> if sel then Size.terminated else id)

  let wrap_item item_cxt expr_cxt expr_cxt' expr' =
    item_cxt expr_cxt (expr_cxt' expr')

  (* dummy apply *)
  (* expression list からダミーの関数適用を作る *)
  let dummy_apply (expr, expr_cxt) children f sel slice =
    if sel then
      let dummy_apply =
        Desc.to_exp
          Desc.e_apply
          (List.map (fun e -> (Nolabel, e)) children) skeleton'
          (hole_of_exp expr) in
      f dummy_apply
    else
      (* 元のコンテキスト *)
      expr_cxt slice

  (* search *)
  let rec search ((children, slice_cxt, expr_cxt), item_cxt) env cxt =

    match children with
    | [] ->
       get' ((slice_cxt id true skeleton', expr_cxt), item_cxt) env cxt

    | first :: rest ->

       let n = Size.get 0 first in

       let g typed sel1 sel2 =

         let slice_cxt' f slice =
           slice_cxt
             f (typed || sel1)
             (if typed then replace2 slice first else slice) in

         let err = not typed in

         if print_slice then
           begin
             print_newline ();
             Format.fprintf
               ppf "@[~SEARCH~@]@.";
             
             Format.fprintf
               ppf "@[slice_cxt : @]@.";
             Format.fprintf
               ppf "  @[fun ■ -> function@]@.";

             let expr' =
               Meta.clean
                 "all" (
                   if err && sel2 then
                     slice_cxt id sel1 first
                   else
                     slice_cxt
                       id true (show_cxt true first)) in

             Format.fprintf
               ppf "  @[| (%a) -> %a@]@."
               print_deb_exp (if n < 0
                              then skeleton' else first)
               print_deb_exp expr';

             Format.fprintf
               ppf "@[%s / %s @]@."
               (if typed then "welltyped" else "illtyped")
               (if typed then
                  if sel1 && sel2 then "backtrack:"
                  else if sel2 then "breadth:"
                  else if sel1 then "depth:"
                  else "abst element:"
                else
                  if sel1 && sel2 then "no bind:"
                  else if sel2 then "abst all:"
                  else if sel1 then "abst one:"
                  else "abst expect:");

             Format.fprintf
               ppf "  @[fun ■ -> %a@]@."
               print_deb_exp (
                 slice_cxt'
                   expr_cxt (show_cxt sel1 first));
           end;

         if err && sel1 && sel2 then
           (* illtyped : no bind *)
           slice_cxt id false skeleton'

         else if err && sel1 then
           (* illtyped : abst one *)
           get ((slice_cxt' id first, expr_cxt), item_cxt) env cxt

         else if err || sel2 then
           (* illtyped : abst one / abst all / no bind / abst expect *)
           (* welltyped : backtrack / breadth *)
           let sel = (typed && sel1) || (err && (sel1 || sel2)) in
           let expr_cxt' sel = if sel then expr_cxt else id in
           get ((slice_cxt' (expr_cxt' sel) first,
                 expr_cxt' (not sel)), item_cxt) env cxt

         else if typed && sel1 then
           (* welltyped : depth *)
           get ((first, slice_cxt' expr_cxt), item_cxt) env cxt

         else
           (* welltyped : abst element *)
           search ((rest, slice_cxt, expr_cxt), item_cxt) env cxt in

       let error sel =
         try

           let structure =
             item_cxt (slice_cxt expr_cxt sel) first in
           ignore (
               Typemod.type_structure env structure Location.none
             );
           raise Not_found
         with
           Typecore.Error _ ->
           g false sel (n < 0) in

       (* 次の処理を決める *)
       try
         assert (rest <> []);
         error false
       with
         _ ->
         try
           error true
         with
           _ ->
           if n < 0 then
             g true false false
           else if 1 < n then
             g true true false
           else if rest = [] then
             g true true true
           else
             g true false true

  and search' ((children, slice_cxt, dummy, sel), item_cxt) env cxt =

    let slice_cxt' =
      if sel then dummy children else slice_cxt in
    let expr_cxt' sel =
      if sel then id else dummy [] id false in

    try
      let structure =
        item_cxt (slice_cxt' (expr_cxt' false) sel) skeleton' in
      ignore (
          Typemod.type_structure env structure Location.none
        );
      (* welltyped *)
      if sel then
        search' ((children, slice_cxt, dummy, false), item_cxt) env cxt
      else
        search ((children, slice_cxt, expr_cxt' false), item_cxt) env cxt
    with
      _ ->
      (* illtyped *)
      let slice = slice_cxt' (expr_cxt' sel) sel skeleton' in

      if print_slice then
        begin
          Format.fprintf
            ppf "@[illtyped / %s @]@."
            (if sel then "no bind" else "abst all");
        end;

      get ((slice, expr_cxt' (not sel)), item_cxt) env cxt

(*
    let expr_cxt' sel =
      if sel then id else dummy [] id false in

    let error sel =

      let slice_cxt' = if sel then dummy children else slice_cxt in
      try
        let structure =
          item_cxt (slice_cxt' (expr_cxt' false) sel) skeleton' in
        ignore (
            Typemod.type_structure env structure Location.none
          );
        (* welltyped *)
        raise Not_found
      with
        Typecore.Error _ ->
        (* illtyped *)
        let slice = slice_cxt' (expr_cxt' sel) sel skeleton' in

        if print_slice then
          begin
          Format.fprintf
            ppf "@[illtyped / %s @]@."
            (if sel then "no bind" else "abst all");
          end;

        get ((slice, expr_cxt' (not sel)), item_cxt) env cxt in

    try
      (* abst all *)
      error false
    with
      _ ->
      try
        (* dummy apply *)
        error true
      with
        _ ->
        search ((children, slice_cxt, expr_cxt' false), item_cxt) env cxt
 *)

  and get ((expr, expr_cxt), item_cxt) env cxt =

    (* 標準の slice_cxt, children *)
    let sel =
      Desc.fold_exp (fun b e -> b && Size.fltr0 e) true expr in

    match expr.pexp_desc with

    | Pexp_ident _ | Pexp_constant _ ->
       (* 変数 / 定数 *)
       get' ((expr, expr_cxt), item_cxt) env cxt

    | Pexp_let (flg, vs, e) when sel ->
       (* let *)
       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~GET~@]@.";
           Format.fprintf
             ppf "@[add cxt / Let %s.%a @]@."
             (if flg = Nonrecursive then "" else "rec ")
             Pprintast.pattern
             (Pat.tuple (List.map (fun {pvb_pat} -> pvb_pat) vs))
         end;
       let expr_cxt' e' =
         Desc.to_exp (Desc.e_let flg) vs e' expr in
       let cxt' = Let (flg, vs, cxt) in
       let slice =
         get' ((e, expr_cxt'),  wrap_item item_cxt expr_cxt) env cxt' in
       get'' cxt env item_cxt (expr_cxt (replace2 slice expr))

    | Pexp_fun (l, eop, p, e) when sel ->

       (* lambda *)
       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~GET~@]@.";
           Format.fprintf
             ppf "@[add cxt / Lambda .%a @]@."
             Pprintast.pattern p
         end;

       let expr_cxt' e' =
         expr_cxt (desc_to_exp (Desc.e_fun l eop p e') expr) in
(*
       let item_cxt' expr_cxt' expr' =
         item_cxt (
             fun e' ->
             expr_cxt (desc_to_exp (Desc.e_fun l eop p e') expr)
           ) (expr_cxt' expr') in
 *)
       let cxt' = Lambda (p, cxt) in
       let slice = get'' cxt' env (wrap_item item_cxt expr_cxt') e in
       get'' cxt env item_cxt (expr_cxt (replace2 slice expr))

    | Pexp_tuple _ | Pexp_array _ ->
       (* expression list *)
       let children = Size.children expr in
       let slice_cxt f sel slice = f (Abst.get expr sel slice) in

       if print_slice then
         begin
           print_newline ();

           Format.fprintf
             ppf "@[~GET (expression slit)~@]@.";

           Format.fprintf
             ppf "@[expr / has %d node(s).: @]@."
             (List.length children);

           Format.fprintf
             ppf "  @[%a@]@."
             print_deb_exp expr;
         end;

       if sel then
         (* ダミーチェック *)
         search' ((children, slice_cxt,
                   dummy_apply (expr, expr_cxt), true), item_cxt) env cxt
       else
         search ((children, slice_cxt, expr_cxt), item_cxt) env cxt


    | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as e))
         when Desc.fold_exp (fun b e -> b && Size.fltr0 e) true e ->

       (* 複数の要素を持つコンストラクタ *)
       let children = Size.children e in

       let slice_cxt f sel slice =
         f (Desc.to_exp
              (Desc.e_construct lid) [] (Abst.get e sel slice) expr) in

       if print_slice then
         begin
           print_newline ();

           Format.fprintf
             ppf "@[~GET (expression list)~@]@.";

           Format.fprintf
             ppf "@[expr / has %d node(s).: @]@."
             (List.length children);

           Format.fprintf
             ppf "  @[%a@]@."
             print_deb_exp expr
         end;

       if List.length children <> List.length es then
         search ((children, slice_cxt, expr_cxt), item_cxt) env cxt
       else
         search' ((children, slice_cxt,
                   dummy_apply (expr, expr_cxt), true), item_cxt) env cxt

    | Pexp_construct (lid, Some e) when sel && Size.fltr1 e ->
       let e' = Size.terminated e in
       let children = match e.pexp_desc with
           Pexp_tuple _ -> Size.children e
         | _ -> [e] in

       (* expr' が slice のとき *)
       let expr_cxt' expr' =
         expr_cxt (Desc.to_exp (Desc.e_construct lid) [] expr' expr) in

       let slice_cxt f sel slice =

         let les =
           List.map (fun e -> (Nolabel, e)) children in
         let expr' =
           Desc.to_exp Desc.e_apply les skeleton' (hole_of_exp expr) in

         if sel && slice = e' then
           (* ダミーをそのまま返す *)
           expr_cxt expr'
         else if sel || slice <> skeleton' then
           (* 要素に対して *)
           f (Abst.get e sel (if slice = e' then skeleton' else slice))
         else
           (* 構成子に関係なく *)
           get ((expr', expr_cxt), item_cxt) env cxt in

       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~GET (construct: %s)~@]@."
             (Longident.last lid.txt);

           Format.fprintf
             ppf "@[expr / has %d node(s).: @]@."
             (List.length children);

           Format.fprintf
             ppf "  @[%a@]@."
             print_deb_exp expr;
         end;

       search ((e' :: children, slice_cxt, expr_cxt'), item_cxt) env cxt
(*
    | Pexp_match (e, cs)  ->
       (* case *)
       if print_slice then
         begin
           print_newline ();
           Format.fprintf
             ppf "@[~GET~@]@.";
           Format.fprintf
             ppf "@[add cxt / Case match @]@.";
         end;
       let expr_cxt' e' =
         Desc.to_exp Desc.e_match cs e' expr in
       let cxt' = Case (Desc.e_match, cs, cxt) in
       let slice = get'' cxt' env (wrap_item item_cxt expr_cxt') e in
       get'' cxt env item_cxt (expr_cxt (replace2 slice expr))
 *)
    | _ ->

       let children = Size.children expr in
       let slice_cxt f sel slice = f (Abst.get expr sel slice) in

       if print_slice then
         begin
           print_newline ();

           Format.fprintf
             ppf "@[~GET~@]@.";

           Format.fprintf
             ppf "@[expr / has %d node(s).: @]@."
             (List.length children);
           Format.fprintf
             ppf "  @[%a@]@."
             print_deb_exp expr;

           if children <> [] then
             Format.fprintf
               ppf "  @[head child is size %d / %d@]@."
               (Size.get 0 (List.hd children))
               (Size.get 0 expr);

         end;

       search ((children, slice_cxt, expr_cxt), item_cxt) env cxt

  and get' ((expr, expr_cxt), item_cxt) env cxt =  match cxt with

    | Lambda (p, _) ->
       (* lambda *)
       let slice = Exp.fun_ Nolabel None p expr in
       if print_slice then
         Format.fprintf
           ppf "@[  return (Lambda): %a@]@."
           print_deb_exp slice;
       slice

    | Let (flg, vs, _) ->
       (* let *)
(*
       let item_cxt' expr_cxt' expr' =
         item_cxt expr_cxt (expr_cxt' expr') in
 *)
       let slice =
         get_vs env item_cxt (flg, (vs, []), get'' Empty env (wrap_item item_cxt expr_cxt) expr) in

       if print_slice then
         Format.fprintf
           ppf "@[  return (Let): %a@]@."
           print_deb_exp slice;
       slice

    | Empty ->

       if Size.fltr0 expr then
         begin
           let slice = Size.terminated (hole_of_exp expr) in
           try
             let structure = item_cxt expr_cxt slice in
             ignore (
                 Typemod.type_structure env structure Location.none
               );
             (* welltyped *)
             if print_slice then
               Format.fprintf
                 ppf "@[  return (no abst) : %a@]@."
                 print_deb_exp expr;
             Size.terminated expr
           with
             Typecore.Error _ ->
             (* illtyped *)
             if print_slice then
               Format.fprintf
                 ppf "@[  return (hole) : %a@]@."
                 print_deb_exp slice;

             slice
         end
       else
         begin
           (* terminated *)
           let slice = expr_cxt expr in
           if print_slice then
             Format.fprintf
               ppf "@[  return (Empty) : %a@]@."
               print_deb_exp slice;
           slice
         end


  and get'' cxt env item_cxt expr = get ((expr, id), item_cxt) env cxt

  (* value binding のスライシング *)
  (* let文のみ *)

  and get_vs env item_cxt (flg, (vs, acc), e) = match vs with
    | [] -> Exp.let_ flg acc e
    | v :: rest ->
       (* value binding の expression をひとつずつ抽象化 *)
       get_vs' env item_cxt (flg, (rest, acc), e) v

  and get_vs' env item_cxt (flg, (rest, acc), e) v =
    let item_cxt' expr_cxt' expr' =
      item_cxt (get_vs'' (flg, (rest, acc), e) v) (expr_cxt' expr') in

    if print_slice then
      Format.fprintf
        ppf "@[  get (value binding) : %a@]@."
        print_deb_strs (item_cxt' id skeleton');

    let v' = Map.v1 (get'' Empty env item_cxt') id v in
    get_vs env item_cxt (flg, (rest, acc @ [v']), e)

  and get_vs'' (flg, (rest, acc), e) v expr =
    Exp.let_ flg (acc @ Map.set_exp Map.v1 v expr :: rest) e

  (* case を含む構文 *)
  (* match / try / function *)

  (* (1) 式部分を抽象化。function では必ず illtyped *)
  (* welltyped : with 前の式のスライシング *)
  (* illtyped  : with 前の式を抽象化して確定 *)
  (* (2) case を全て抽象化 *)
  (* welltyped : 先頭のcaseの抽象化。
     その後、無視するとwelltypedになるcaseがあれば抽象化。 *)
  (* illtyped : すべて確定 *)

end


module Structure_slicing : sig

  (* structure のスライシング *)
  val get :
    (structure_cxt * structure_item * structure) context_t -> structure

end = struct

  (* search *)
  (* structure のスライスを1行ずつ求める。 *)
  let rec search (str_cxt, prefix, slice_str) cxt = match prefix with
      [] -> str_cxt [] slice_str
    | (next_str, env) :: rest ->
       try
         let (s', env') = List.hd rest in
         ignore (Typemod.type_structure
                   env' (str_cxt rest (s' :: slice_str)) Location.none);
         raise Not_found
       with
       | Typecore.Error _ ->
          (* Typecore.Error *)
          (* next_str を無視しても型エラーが残る *)
          if print_slice then
            Format.fprintf ppf "@[ignore: %a@]@."
                           print_deb_strs [next_str];
          search (str_cxt, rest, slice_str) cxt
       | _ ->
          (* Typetexp.Error, slice_str が空 *)
          (* next_str を無視したら型エラーが消える *)
          go get rest env cxt (str_cxt, next_str, slice_str)

  (* 着目している行のスライスを求める。 *)
  and get (((str_cxt, item, slice_str), cxt), env, prefix) = match item with
      {pstr_desc = d; pstr_loc = loc} ->
      (* item をスライシングして、slice_str を更新する。 *)      
      let slice_str' = match d with
        | Pstr_eval (expr, _) ->
           (* eval *)
           let eval_cxt e = (Str.eval ~loc e) :: slice_str in
           go eval prefix env cxt
              (str_cxt, eval_cxt, go Complete.expression prefix env cxt expr)
        (*           eval (((str_cxt, (eval_cxt, expr), slice_str), cxt), env, prefix) *)
        | Pstr_value (flg, vs) when item <> hole_str ->
           (* value *)
           let value_cxt vs = (Str.value ~loc flg vs) :: slice_str in
           if print_slice then
             Format.fprintf ppf "@[~go to complete~@]@.";
           go value prefix env cxt
              (str_cxt, value_cxt, go Complete.value_bindings prefix env cxt vs)
(*
           let vs' = Complete.value_bindings ((vs, cxt), env, prefix) in
           value (((str_cxt, (value_cxt, vs'), slice_str), cxt), env, prefix) *)
        | Pstr_module ({pmb_loc; pmb_name = name;
                        pmb_expr = {pmod_loc; pmod_attributes = [];
                                    pmod_desc = Pmod_structure (mod_str)}}) ->
           (* module *)
           let me_cxt str =
             Mod.structure ~loc:pmod_loc
                           ~attrs:[mkloc "mod" loc, PStr mod_str;
                                   mknoloc "size", Size (List.length mod_str)] str in
           let mb_cxt str =
             Mb.mk ~loc:pmb_loc name (me_cxt str) in
           let mod_cxt str =
             (Str.module_ ~loc (mb_cxt str)) :: slice_str in
           let str_cxt' prefix' structure' =
             mod_cxt (
                 List.fold_left (
                     fun str (s', _) -> s' :: str) structure' prefix') in
           go module_ [] env cxt (str_cxt', mod_str)
(*           module_ (((mod_str, str_cxt'), cxt), env, []) *)
        | _ -> item :: slice_str in

      (* search に移動 *)
      search (str_cxt, prefix, slice_str') cxt

  (* get' *)
  (* Expression_slicing に行く *)
  (* ひとつ前の行の環境があれば使う。なければ現在の環境を使う。 *)
  and get' (((str_cxt, f, expr), cxt), env, prefix) =

    let slice_cxt prefix str exp_cxt slice =
      str_cxt prefix (str @ f (exp_cxt slice)) in

    let (item_cxt, env') = match prefix with
        [] -> (slice_cxt prefix [], env)
      | (s', env') :: prefix' ->
         try
           ignore (
               Typemod.type_structure env (f skeleton') Location.none);
           (* □に置き換えて welltyped: *)
           (slice_cxt prefix [], env)
         with _ ->
           (* □に置き換えて illtyped: *)
           (slice_cxt prefix' [s'], env') in


(*
    try
      (* デバッグモード *)
      (* txtファイルとして出力。表データの形式になる *)
      assert (Sys.argv.(2) = "debug");

      Format.fprintf ppf "@[~debugmode~@]@.";
      ExprSlicingDebugger.getLine expr item_cxt env' cxt
    with
      _ ->
 *)
    if true then
      ExprSlicingDebugger.getLine expr item_cxt env' cxt

    else

    (* expression slicing *)
    if false then (* 古いバージョン *)
      Expression_slicing.get ((expr, id), item_cxt) env' cxt

    else if true then
      (* 実験用：新しいslicing1 とslicing2 *)


      let (slice1, time1, typed1) =
        let begin_time = Sys.time () in
        let slice =
          ExprSlicing1.top expr item_cxt env' cxt in
        let end_time = Sys.time () in
        (Meta.clean "all" slice,
         end_time -. begin_time,
         ExprSlicing.typed env' item_cxt id slice) in

      let (slice2, time2, typed2) =
        let begin_time = Sys.time () in
        let slice =
          ExprSlicing2.top expr item_cxt env' cxt in
        let end_time = Sys.time () in
        (Meta.clean "all" slice,
         end_time -. begin_time,
         ExprSlicing.typed env' item_cxt id slice) in

      let (slice3, time3, typed3) =
        let begin_time = Sys.time () in
        let slice =
          ExprSlicing3.top expr item_cxt env' cxt in
        let end_time = Sys.time () in
        (Meta.clean "all" slice,
         end_time -. begin_time,
         ExprSlicing.typed env' item_cxt id slice) in


      if print_slice then
        begin
          if slice1 = slice2 then
            Format.fprintf
              ppf "@[slice 1 and 2 are same.@]@.";
          if slice1 = slice3 then
            Format.fprintf
              ppf "@[slice 1 and 3 are same.@]@.";

          Format.fprintf
            ppf "@[original slicing : %f sec.@]@." time1;
          Format.fprintf
            ppf "@[  %s : %a @]@."
            (if typed1 then "welltyped" else "illtyped")
            Pprintast.expression slice1;

          Format.fprintf
            ppf "@[resize slicing : %f sec.@]@." time2;
          Format.fprintf
            ppf "@[  %s : %a@]@."
            (if typed2 then "welltyped" else "illtyped")
            Pprintast.expression slice2;

          Format.fprintf
            ppf "@[sort slicing : %f sec.@]@." time3;
          Format.fprintf
            ppf "@[  %s : %a@]@."
            (if typed3 then "welltyped" else "illtyped")
            Pprintast.expression slice3;
        end;

      slice1

    else if false then
      Expression_slicing'.top (Size.set expr) item_cxt env' Empty 


    else if false then (* 現在のバージョン *)
      Meta.clean
        "all"
        (Expression_slicing''.get ((Size.set expr, id), item_cxt) env' Empty)
    else (* 比較 *)
      begin

        let begin_time1 = Sys.time () in
        let return1 =
          Expression_slicing.get ((expr, id), item_cxt) env' cxt in
        let end_time1 = Sys.time () in

        let begin_time2 = Sys.time () in
        let return2 =
          Expression_slicing'.get ((Size.set expr, id), item_cxt) env' Empty in
        let end_time2 = Sys.time () in

        let begin_time3 = Sys.time () in
        let return3 =
          Expression_slicing''.get ((Size.set expr, id), item_cxt) env' Empty in
        let end_time3 = Sys.time () in

        let begin_time4 = Sys.time () in
        let return4 =
          Expression_slicingNoResize.get
            ((Size.set expr, id), item_cxt) env' Empty in
        let end_time4 = Sys.time () in

        if print_slice then
          print_newline ();

        if print_slice then
          Format.fprintf ppf "@[(slicing 1) %a(%f sec.)@]@."
                         Pprintast.expression (Meta.clean "all" return1)
                         (end_time1 -. begin_time1);

        if print_slice then
          Format.fprintf ppf "@[(slicing 2) %a(%f sec.)@]@."
                         Pprintast.expression (Meta.clean "all" return2)
                         (end_time2 -. begin_time2);

        if print_slice then
          Format.fprintf ppf "@[(slicing 3) %a(%f sec.)@]@."
                         Pprintast.expression (Meta.clean "all" return3)
                         (end_time3 -. begin_time3);

        if print_slice then
          Format.fprintf ppf "@[(slicing 4) %a(%f sec.)@]@."
                         Pprintast.expression (Meta.clean "all" return4)
                         (end_time4 -. begin_time4);

(*
        if print_slice &&
             Meta.clean "all" return1 = Meta.clean "all" return2 then
          Format.fprintf ppf "@[they are same.@]@.";
 *)
        return1
      end


  (* Eval : (structure_cxt * (expression -> structure) * expression) context_t
     -> structure *)
  (* eval のスライシング *)
  and eval (((str_cxt, eval_cxt, expr), cxt), env, prefix) =
    let slice =
      go get' prefix env cxt (str_cxt, eval_cxt, expr) in
    if print_slice then
      Format.fprintf ppf "@[get_slice_eval: %a @]@."
                     print_deb_strs (eval_cxt slice);
    eval_cxt slice

  (* value *)
  (* value のスライシング *)
  and value (((str_cxt, value_cxt, vs), cxt), env, prefix) = match vs with
      [] -> value_cxt []
    | vn :: rest ->
       (* vn のスライスを求める *)
       let value_cxt' e vs' = value_cxt ((Map.set_exp Map.v1 vn e) :: vs') in
       let vb_cxt e = value_cxt' e rest in
       let slice =
         go get' prefix env cxt (str_cxt, vb_cxt, vn.pvb_expr) in
       if print_slice then
         Format.fprintf ppf "@[get_slice_value: %a @]@."
                        print_deb_strs (value_cxt' slice []);
       go value prefix env cxt (str_cxt, value_cxt' slice, rest)

  (* module *)
  (* (structure_cxt * (structure -> structure) * structure) context_t
     -> structure *)
  (* module のスライシング *)
  and module_ (((str_cxt, structure), cxt), env, prefix) = match structure with
    | [] -> search (str_cxt, prefix, []) cxt
    | s :: rest ->
       try
         (* rest のみ無視したモジュールで型がつくかどうかチェックする *)
         ignore (
             Typemod.type_structure
               env [List.hd (str_cxt prefix [s])] Location.none);
         (* prefix に積んで再帰 *)
         go module_ ((s, env) :: prefix) env cxt (str_cxt, rest)
       with _ ->
         (* モジュールの中で型エラー *)
         go get prefix env cxt (str_cxt, s, [])

end


let rec top structure env prefix = match structure with
    [] -> failwith "TypeDebugger: Error: structure is well typed."
  | s :: rest ->
     try
       let (_, _, env') =
         Typemod.type_structure env [s] Location.none in
       top rest env' ((s, env) :: prefix)
     with _ ->
       let structure_cxt _ str = str in
       Structure_slicing.get (((structure_cxt, s, []), Empty), env, prefix)


(* ここから：デバッグ用のスライス書き込み *)

module type Go =
  sig
    type t
    val go : unit -> t
  end

module type InitTop =
  sig
    type t = structure
    val name : string
    val context :
      ((structure_item * structure) * structure_cxt) context_t
  end

module type InitSlice =
  sig
    type t
    val slice : t
    val cxt : expr_context
    val typed_set : ((t -> t) -> t -> structure) * Env.t
  end

module type Init =
  sig
    type t
    val env : Env.t
  end

module type Slicer =
  sig
    type t
    val get : (t * (t -> t)) * ((t -> t) -> t -> structure) -> expr_context ->t
  end

module type MakeSlicer =
  sig
    type slice
    module type Init = Init with type t = slice
    module type Slicer = Slicer with type t = slice
    module type Make = functor (I : Init) -> Slicer
    val get : (module InitSlice with type t = slice) -> string -> slice
  end

type 'a make_slicer = (module MakeSlicer with type slice = 'a)

module Get =
  struct

    (* context_t の生成 *)
    let rec context' structure env prefix = match structure with
        [] -> failwith "TypeDebugger: Error: structure is well typed."
      | s :: rest ->
         try
           let (_, _, env') =
             Typemod.type_structure env [s] Location.none in
           context' rest env' ((s, env) :: prefix)
         with _ ->
           ((((s, []), fun _ x -> x), Empty), env, prefix)

    (* init の生成 *)
    let init (type s) env =
      (module
         struct
           type t = s
           let env = env
         end : Init with type t = s)

    let initTop name structure env =
      (module
         struct
           type t = structure
           let name = name
           let context = context' structure env []
         end : InitTop)

    let initSlice (type s) skeleton ((((f, slice), str_cxt), cxt), env, prefix) = 
        let item_cxt' prefix str slice_cxt slice' =
          str_cxt prefix (str @ f (slice_cxt slice')) in
        (module
           struct
             type t = s
             let slice = slice
             let cxt = cxt
             let typed_set = match prefix with
                 [] -> (item_cxt' prefix [], env)
               | (s', env') :: prefix' ->
                  try
                    ignore (
                        Typemod.type_structure env (f skeleton) Location.none);
                    (* □に置き換えて welltyped: *)
                    (item_cxt' prefix [], env)
                  with _ ->
                    (* □に置き換えて illtyped: *)
                    (item_cxt' prefix' [s'], env')
           end : InitSlice with type t = s)

    (* スライスを求める *)
    let slice (type s) slice item_cxt cxt (module S : Slicer with type t = s) =
      S.get ((slice, id), item_cxt) cxt

    let slicer (type s) name skeleton context
               (module M : MakeSlicer with type slice = s) =
      (module
         struct
           type t = s
           let go () = M.get (initSlice skeleton context) name
         end : Go with type t = s)

    let f (type s) (module F : Go with type t = s) = F.go ()

  end

module ExprSlicer :
  sig
    val make : expression make_slicer
    val find : string -> bool
  end = struct

    module Make =
      struct
        type slice = expression
        module type Slicer = Slicer with type t = expression
        module type Init = Init with type t = expression
        module type Make = functor (I : Init) -> Slicer
        let print = print_deb_exp
        let term e = Size.reset e
        let hole e = term (hole_of_exp e)
        let make_slicer (module M : Make) (module I : Init) =
          (module M (I) : Slicer)
            
        let print_slice = false
        include Times
                  
        let typed' e b =
          if print_slice then
            Format.fprintf ppf "    @[%s: %a @]@."
                           (if b then "welltyped" else "illtyped")
                           print_deb_exp e;
          b
            
        let typed (item_cxt, env) expr_cxt expr =
          let t = Sys.time () in
          let return = typed' (expr_cxt expr) in
          try
            ignore
              (Typemod.type_structure env (item_cxt expr_cxt expr) Location.none);
            set (Sys.time () -. t);
            return true
          with
            _ ->
            set (Sys.time () -. t);
            return false
                   
        let selector = ref true
                           
        module Slicer1 (I : Init) = struct
          include I
                    
          let wrap_expr expr_cxt' expr_cxt expr =
            expr_cxt' (expr_cxt expr)
          let wrap_item item_cxt expr_cxt' expr_cxt expr =
            item_cxt (wrap_expr expr_cxt' expr_cxt) expr
                     
          let dummy_apply expr es =
            if List.exists (fun e -> e = hole e) es then []
            else
              [{expr with
                 pexp_desc =
                   Pexp_apply (hole expr, List.map (fun e -> (Nolabel, e)) es)}]
                
          let abst sel e' e = match Desc.comp_loc_exp e' e with
              1 -> if sel then e else hole e
            | 0 -> e'
            | _ -> if sel then hole e else e
                                             
          let make_expr expr e' =
            Desc.map_exp (abst false e') expr
                         
          let selected_expr expr expr_cxt' e' =
            if Desc.comp_loc_exp e' expr < 0 then expr_cxt' e' else e'
                                                                      
          (* dummy apply *)
          let getChildren'' expr = match expr.pexp_desc with
            | Pexp_tuple es ->
               dummy_apply expr es
            | Pexp_array es ->
               dummy_apply expr es
            | Pexp_construct (_, Some {pexp_desc = Pexp_tuple es}) ->
               dummy_apply expr es
            | _ -> []
                     
          (* □以外の子ノード全て *)
          let getChildren' expr = match expr.pexp_desc with
            | Pexp_construct (_, Some {pexp_desc = Pexp_tuple es}) ->
               List.filter (fun e -> e <> hole e) es
            | _ ->
               Desc.fold_exp (
                   fun acc e ->
                   if Size.fltr0 e then e :: acc else acc
                 ) [] expr
                             
          let getChildren expr =
            if false then
              getChildren'' expr @ getChildren' expr
            else
              getChildren' expr
                           
          let rec search (slices, expr_cxt, item_cxt, f) cxt = match slices with
            | [] -> f ()
            | first :: rest ->
               if print_slice then
                 Format.fprintf ppf "@[  search: %a @]@."
                                print first;
           if typed (item_cxt, env) expr_cxt first then
             (* welltyped *)
             search (rest, expr_cxt, item_cxt, f) cxt
           else
             (* illtyped *)
             get ((expr_cxt first, id), item_cxt) cxt
                 
          and get ((expr, expr_cxt), item_cxt) cxt =
            
            if print_slice then
              Format.fprintf ppf "@[  get: %a @]@."
                             print expr;
            
            let children = getChildren expr in
            
            match expr.pexp_desc with
              
            | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as expr')) ->
               
               (* Construct *)
               let fold es' e' =
                 {expr with
                   pexp_desc =
                     Pexp_construct (
                         lid,
                         Some {expr' with
                                pexp_desc =
                                  Pexp_tuple (List.map (abst false e') es')})} in
               let f () =
                 let slice =
                   let fold' es' e' = fold es' (Size.reset e') in
                   let es' =
                     Desc.fold_exp (
                         fun es' e ->
                         let slice =
                           get' ((e, id), wrap_item item_cxt (fold' es')) cxt in
                         List.map (
                             fun e ->
                             if Desc.comp_loc_exp slice e < 0 then e else slice) es'
                       ) es expr' in
                   fold' es' skeleton' in
                 wrap_expr expr_cxt Size.reset slice in
               
               (* search *)
               search (
                   children,
                   wrap_expr expr_cxt (selected_expr expr (fold es)),
                   item_cxt, f) cxt
                      
            | _ ->
               
               let f () =
                 let slice =
                   let item_cxt' = wrap_item item_cxt expr_cxt in
                   Desc.fold_exp (
                       fun expr' e ->
                       let expr_cxt'' = make_expr expr' in
                       let item_cxt'' = wrap_item item_cxt' expr_cxt'' in          
                       get' ((e, id), item_cxt'') cxt |> expr_cxt''
                     ) expr expr in
                 wrap_expr expr_cxt Size.reset slice in
               
               (* search *)
               search (
                   children,
                   wrap_expr expr_cxt (selected_expr expr (make_expr expr)),
                   item_cxt, f) cxt
                      
          (* get' *)
          and get' ((expr, expr_cxt), item_cxt) cxt =
            if Desc.leaf_exp expr then wrap_expr expr_cxt Size.reset expr
            else get ((expr, expr_cxt), item_cxt) cxt
                     
        end
                                      
        module Slicer2 (I : Init) =
          struct
            include I
                      
            let rec search (child, sel, expr_cxt, slice_cxt) item_cxt cxt =
              
              if print_slice then
                Format.fprintf ppf "@[  search / abst %s: %a @]@."
                               (if sel then "expect" else "one")
                               print child;
              
              let sel' =
                typed (item_cxt, env) (slice_cxt sel expr_cxt) child in
              
              if sel' && sel then
                (* welltyped : abst expect *)
                search (child, false, expr_cxt, slice_cxt) item_cxt cxt
                       
              else
                let g pair = get (pair, item_cxt) cxt in
                
                if sel' && Size.is1 child then
                  (* welltyped : is1 *)
                  g (slice_cxt false expr_cxt (Size.reset child), id)
                    
                else if sel' || sel then
                  (* welltyped : greater1 *)
                  (* illtyped : abst expect *)
                  g (child, slice_cxt sel expr_cxt)
                    
                else
                  (* illtyped : abst one *)
                  g (slice_cxt sel id child , expr_cxt)
                    
            and get ((expr, expr_cxt), item_cxt) cxt =
              
              if print_slice then
                Format.fprintf ppf "@[  get: %a @]@."
                               print expr;
              
              if Size.fltr1 expr then
                let (expr', slice_cxt) =
                  if !selector then
                    Size.getChildSet expr
                  else
                    Size.getChildSet2 expr in
                search (expr',
                        slice_cxt true id expr' <> expr, expr_cxt,
                        slice_cxt) item_cxt cxt
              else
                get' ((expr, expr_cxt), item_cxt) cxt
                     
            and get' ((expr, expr_cxt), item_cxt) cxt =
              let slice = expr_cxt expr in
              if Size.fltr0 slice then
                get ((slice, id), item_cxt) cxt
              else
                slice
          end
            
        module Slicer3 (I : Init) = struct
          include I
                    
          (* search *)
          let rec search ((children, slice_cxt), expr_cxt) item_cxt cxt =
            match children with
            | [] -> get' ((slice_cxt id true skeleton', expr_cxt), item_cxt) cxt
            | first :: rest ->
               if print_slice then
                 Format.fprintf ppf "@[  search: %a @]@."
                                print first;
               
               let n = Size.get 0 first in
               
               let g typed sel1 sel2 =
                 
                 let slice_cxt' f slice =
                   slice_cxt
                     f (typed || sel1)
                     (if typed then term {first with pexp_desc = slice.pexp_desc}
                      else slice) in
                 
                 let err = not typed in
                 
                 if err && sel1 && sel2 then
                   (* illtyped : no bind *)
                   slice_cxt id false skeleton'
                             
                 else if err && sel1 then
                   (* illtyped : abst one *)
                   get ((slice_cxt' id first, expr_cxt), item_cxt) cxt
                       
                 else if err || sel2 then
                   (* illtyped : abst one / abst all / no bind / abst expect *)
                   (* welltyped : backtrack / breadth *)
                   let sel = (typed && sel1) || (err && (sel1 || sel2)) in
                   let expr_cxt' sel = if sel then expr_cxt else id in
                   get ((slice_cxt' (expr_cxt' sel) first,
                         expr_cxt' (not sel)), item_cxt) cxt
                       
                 else if typed && sel1 then
                   (* welltyped : depth *)
                   get ((first, slice_cxt' expr_cxt), item_cxt) cxt
                       
                 else
                   (* welltyped : abst element *)
                   search ((rest, slice_cxt), expr_cxt) item_cxt cxt in
               
               let error sel =
                 assert (not (typed (item_cxt, env) (slice_cxt expr_cxt sel) first));
                 g false sel (n < 0) in
               (* 次の処理を決める *)
               try
                 assert (rest <> []);
                 error false
               with
                 _ ->
                 try
                   error true
                 with
                   _ ->
                   if n < 0 then
                     g true false false
                   else if 1 < n then
                     g true true false
                   else if rest = [] then
                     g true true true
                   else
                     g true false true
                       
          and get ((expr, expr_cxt), item_cxt) cxt =
            
            if print_slice then
              Format.fprintf ppf "@[  get: %a @]@."
                             print expr;        
            
            if Desc.leaf_exp expr then
              (* 変数 / 定数 *)
              get' ((expr, expr_cxt), item_cxt) cxt
                   
            else
              let childrenSet = match expr.pexp_desc with
                | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple _} as e)) ->
                   (Size.children e,
                    fun expr_cxt' sel e' ->
                    expr_cxt'
                      {expr with
                        pexp_desc = 
                          Pexp_construct (lid, Some (Abst.get e sel e'))})   
                | _ ->
                   (Size.children expr,
                    fun expr_cxt' sel e' ->
                    expr_cxt' (Abst.get expr sel e')) in
              search (childrenSet, expr_cxt) item_cxt cxt
                     
          and get' ((expr, expr_cxt), item_cxt) _ =
            
            if Size.fltr0 expr then
              let slice' = hole expr in
              if typed (item_cxt, env) expr_cxt slice' then
                term expr
              else
                slice'
            else
              expr_cxt expr

        end
                       
        (* fileを扱う *)
(*        let write ?(c = "	") file str = output_string file (c ^ str)
        let write_expr ?(c = "	") file e = 
          Pprintast.string_of_expression e
          |> String.split_on_char '\n'
          |> String.concat "<br>"
          |> write ~c:c file
        let set_ file expr =
          set 0.;
          write_expr ~c:"\n" file expr;
          Size.set expr *)
                   
        let list : (string * (module Make)) list =
          ["original", (module Slicer1);
           "resize1", (module Slicer2);
           "resize2", (module Slicer2);
           "sort", (module Slicer3)]

        let find name =
          List.exists (fun (name', _) -> name = name') list

        (* get_one *)
        let get_one ?(all = true)  (module S : InitSlice with type t = expression) (name, make) =
          let open S in
          ignore(all = true);
          if name = "resize1" (* 大きいものを選んでいく方 *) then
              selector := true
          else if name = "resize2" then
            selector := false;
          (* let file =
            if name = "resize1" then
              selector := true
            else if name = "resize2" then
              selector := false;
            let filename = 
              "result"
              ^ (if all then "_of_" ^ name else "")
              ^ ".txt" in
            open_out_gen
              [Open_append; Open_creat]
              0o777 filename in *)

          let result =
            let expr = Size.set slice (* set_ file slice *) in
            try
              assert (Desc.leaf_exp expr);
              if typed typed_set hole expr then
                term expr
              else
                hole expr
            with
              _ ->
              Get.init (snd typed_set)
              |> make_slicer make
              |> Get.slice expr (fst typed_set) cxt in

          (* write_expr file (Meta.clean "all" result);
          cnt () |> string_of_int |> write file;
          time () |> string_of_float |> write file;
          close_out file; *)
          result


        (* get_all *)
        let get_all init = List.map (get_one init) list

        let get init name =
          try
            get_one ~all:false init (name, List.assoc name list)
          with
            Not_found -> List.hd (get_all init)

      end

    let make =
      (module Make : MakeSlicer with type slice = expression)
    let find = Make.find
  end

(* 共通部分 *)
module Top (I : InitTop) =
  struct
    type t = structure

    (* search *)
    (* structure のスライスを1行ずつ求める。 *)
    let rec search (str_cxt, prefix, slice_str) cxt = match prefix with
        [] -> str_cxt [] slice_str
      | (next_str, env) :: rest ->
         try
           let (s', env') = List.hd rest in
           ignore (Typemod.type_structure
                     env' (str_cxt rest (s' :: slice_str)) Location.none);
           raise Not_found
         with
         | Typecore.Error _ ->
            (* Typecore.Error *)
            (* next_str を無視しても型エラーが残る *)
            if print_slice then
              Format.fprintf ppf "@[ignore: %a@]@."
                             print_deb_strs [next_str];
            search (str_cxt, rest, slice_str) cxt
         | _ ->
            (* Typetexp.Error, slice_str が空 *)
            (* next_str を無視したら型エラーが消える *)
            go get rest env cxt ((next_str, slice_str), str_cxt)

    (* 着目している行のスライスを求める。 *)
    and get ((((item, slice_str), str_cxt), cxt), env, prefix) =
      match item with
        {pstr_desc = d; pstr_loc = loc} ->
        (* item をスライシングして、slice_str を更新する。 *)      
        let slice_str' = match d with
          | Pstr_eval (expr, _) ->
             (* eval *)
             let eval_cxt e = (Str.eval ~loc e) :: slice_str in
             go eval prefix env cxt
                (str_cxt, eval_cxt, go Complete.expression prefix env cxt expr)
          | Pstr_value (flg, vs) when item <> hole_str ->
             (* value *)
             let value_cxt vs = (Str.value ~loc flg vs) :: slice_str in
             if print_slice then
               Format.fprintf ppf "@[~go to complete~@]@.";
             go value prefix env cxt
                (str_cxt, value_cxt, go Complete.value_bindings prefix env cxt vs)
          | Pstr_module ({pmb_loc; pmb_name = name;
                          pmb_expr = {pmod_loc; pmod_attributes = [];
                                      pmod_desc = Pmod_structure (mod_str)}}) ->
             (* module *)
             let me_cxt str =
               Mod.structure ~loc:pmod_loc
                             ~attrs:[mkloc "mod" loc, PStr mod_str;
                                     mknoloc "size", Size (List.length mod_str)] str in
             let mb_cxt str =
               Mb.mk ~loc:pmb_loc name (me_cxt str) in
             let mod_cxt str =
               (Str.module_ ~loc (mb_cxt str)) :: slice_str in
             go module_
                [] env cxt
                (mod_str,
                 fun prefix' structure' ->
                 mod_cxt (
                     List.fold_left (
                         fun str (s', _) ->
                         s' :: str) structure' prefix'))
          | _ -> item :: slice_str in
        
        (* search に移動 *)
        search (str_cxt, prefix, slice_str') cxt
               
    (* Eval : (structure_cxt * (expression -> structure) * expression) context_t
     -> structure *)
    (* eval のスライシング *)
    and eval (((str_cxt, eval_cxt, expr), cxt), env, prefix) =
      let slice =
        go get' prefix env cxt ((eval_cxt, expr), str_cxt) in
      if print_slice then
        Format.fprintf ppf "@[get_slice_eval: %a @]@."
                       print_deb_strs (eval_cxt slice);
      eval_cxt slice

    (* value *)
    (* value のスライシング *)
    and value (((str_cxt, value_cxt, vs), cxt), env, prefix) = match vs with
        [] -> value_cxt []
      | vn :: rest ->
         (* vn のスライスを求める *)
         let value_cxt' e vs' = value_cxt ((Map.set_exp Map.v1 vn e) :: vs') in
         let vb_cxt e = value_cxt' e rest in
         let slice =
           go get' prefix env cxt ((vb_cxt, vn.pvb_expr), str_cxt) in
         if print_slice then
           Format.fprintf ppf "@[get_slice_value: %a @]@."
                          print_deb_strs (value_cxt' slice []);
         go value prefix env cxt (str_cxt, value_cxt' slice, rest)

    (* module *)
    (* (structure_cxt * (structure -> structure) * structure) context_t
     -> structure *)
    (* module のスライシング *)
    and module_ (((structure, structure_cxt), cxt), env, prefix) =
      match structure with
        [] -> search (structure_cxt, prefix, []) cxt
      | s :: rest ->
         try
           (* rest のみ無視したモジュールで型がつくかどうかチェックする *)
           ignore (
               Typemod.type_structure
                 env [List.hd (structure_cxt prefix [s])] Location.none);
           (* prefix に積んで再帰 *)
           go module_ ((s, env) :: prefix) env cxt (rest, structure_cxt)
         with _ ->
           (* モジュールの中で型エラー *)
           go get prefix env cxt ((s, []), structure_cxt)

    (* get' *)
    (* Expression_slicing に行く *)
    (* ひとつ前の行の環境があれば使う。なければ現在の環境を使う。 *)
    and get' context =
      Get.f (Get.slicer I.name skeleton' context ExprSlicer.make)

    (* ここから呼び出す *)
    let go () =
      let structure = get I.context in
      (* if ExprSlicer.find I.name then *)
        structure
      (* else
        failwith "Slicer: debug mode" *)

  end
(* ここまで：デバッグ用のスライス書き込み *)

let get_slice_top structure env =
  Warnings.parse_options false "-A";

  if false then
    top structure env []
  else
    (* "" がどのスライサを動かしているかに対応している *)
    let (module I : InitTop) = Get.initTop "resize1" structure env in
    Get.f (module Top (I) : Go with type t = structure)
