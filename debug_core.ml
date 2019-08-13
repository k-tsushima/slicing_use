(* This file is written by Naho Wakikawa, Kenichi Asai and Kanae Tsushima. *)


open Asttypes
open Ast_helper

open Types
open Typedtree

open Parsetree

(* ppf *)
let ppf = Format.std_formatter

(* コンテキストの定義 *)
type expr_context =
  Empty
| Lambda of pattern * expr_context
| Let of rec_flag * value_binding list * expr_context
type 'a context_t =
  ('a * expr_context) * Env.t * (structure_item * Env.t) list

(* ---------------------------------------------------------- *)

(* map 関数の集合 *)
module Map = struct

  type 'a map2 = (pattern -> expression -> expression)
                 -> (pattern -> expression -> pattern)
                 -> 'a -> 'a
  type 'a map1 = (expression -> expression) -> (pattern -> pattern)
                 -> 'a -> 'a

  let x1to2 x2 fe fp x = x2 (fun _ e -> fe e) (fun p _ -> fp p) x

  (* 2引数 *)
  let v2 fe2 fp2 ({pvb_pat = p; pvb_expr = e} as v) =
    {v with pvb_pat = fp2 p e; pvb_expr = fe2 p e}
  let c2 fe2 fp2 ({pc_lhs = p; pc_rhs = e} as c) =
    {c with pc_lhs = fp2 p e; pc_rhs = fe2 p e}

  (* 1引数 *)
  let v1 fe fp v = x1to2 v2 fe fp v
  let c1 fe fp c = x1to2 c2 fe fp c
  let e1 fe _ e = fe e
  let p1 _ fp p = fp p
  let le fe _ (l, e) = (l, fe e)
  let lp _ fp (l, p) = (l, fp p)
  let id = fun x -> x

  (* 差し替え *)
  let set_exp x1 x e = x1 (fun _ -> e) id x
  let set_pat x1 x p = x1 id (fun _ -> p) x

  (* 式の抜き出し *)
  let e_in_v v = v.pvb_expr
  let e_in_c c = c.pc_rhs

end

(* ホール *)
module Hole = struct

  (* □の種類 *)
  (* Exp : 式の□ *)
  (* Pat : パターンの□ *)
  (* Hole : 抽象化の必要がない *)
  type t = Exp of attribute
         | Pat of attribute
         | Hole
  (* □を求める関数 *)
  (* Abst.hole' : ?exp:expression -> ?pat:pattern -> unit -> Abst.t *)
  let rec hole' ?(exp = dummy_assertfalse ()) ?(pat = dummy_any ()) () =
    match (exp, pat) with
    | ({pexp_loc = loc; pexp_attributes = []}, _) when
           exp <> dummy_assertfalse ~loc () && pat = dummy_any () ->
       Exp ({txt = "exp"; loc}, PPat (pat, Some (exp))) (* 式の□ *)
    | (_, {ppat_loc = loc; ppat_attributes = []}) when
           exp = dummy_assertfalse () && pat <> dummy_any ~loc () ->
       Pat ({txt = "pat"; loc}, PPat (pat, None)) (* パターンの□ *)
    | _ -> Hole (* 既に抽象化されている *)
  (* 式の抽象化 *)
  (* Abst.expression : expression -> expression *)
  and expression exp = match hole' ~exp () with
    | Exp attr -> Exp.attr (dummy_assertfalse ~loc:exp.pexp_loc ()) attr
    | _ -> exp
  (* パターンの抽象化 *)
  (* Abst.pattern : pattern -> pattern *)
  and pattern pat = match hole' ~pat () with
    | Pat attr -> Pat.attr (dummy_any ~loc:pat.ppat_loc ()) attr
    | _ -> pat
  (* ダミーの作成 *)
  (* dummy_any : ~loc:loc -> unit -> pattern *)
  (* その他 : ~loc:loc -> unit -> expression *)
  and dummy_any ?(loc = Location.none) () =
    Pat.any ~loc ()
  and dummy_false ?(loc = Location.none) () =
    Exp.construct ~loc (mknoloc (Longident.Lident "false")) None
  and dummy_assertfalse ?(loc = Location.none) () =
    Exp.assert_ ~loc (dummy_false ())
  and dummy_int0 ?(loc = Location.none) () =
    Exp.constant ~loc (Const.int 0)
  and dummy_fun ?(loc = Location.none) () =
    Exp.fun_ ~loc Nolabel None (dummy_any ()) (dummy_assertfalse ())

  (* 変数として□を呼び出す用：lidになっている *)
  let skeleton = mknoloc (Longident.parse "□")

  (* □ を定義する structure_item *)
  let item =
    (* let □ = assert false *)
    let p = Pat.var (mknoloc "□") in
    let e = dummy_assertfalse () in
    let vs = [Vb.mk p e] in
    Str.value Nonrecursive vs

  (* 式のホール *)
  let hole_of_exp ({pexp_loc = loc; pexp_attributes = attrs} as exp) =
    if List.exists (fun ({txt = name}, _) -> name = "exp") attrs
    then exp (* 追加しなくて良い *)
    else
      let attrs = (mkloc "exp" loc, PStr [Str.eval ~loc exp]) :: attrs in
      Exp.ident ~loc ~attrs skeleton

(*
    if attrs = [] then
      let attrs = (mkloc "exp" loc, PStr [Str.eval ~loc exp]) :: attrs in
      Exp.ident ~loc ~attrs skeleton
    else exp
 *)

  (* パターンのホール *)
  let hole_of_pat ({ppat_loc = loc; ppat_attributes = attrs} as pat) =
    if List.exists (fun ({txt = name}, _) -> name = "pat") attrs
    then pat (* 追加しなくて良い *)
    else
      let attrs = (mkloc "pat" loc, PPat (pat, None)) :: attrs in
      Pat.any ~loc ~attrs ()
(*
    if attrs = [] then
      let attrs = (mkloc "pat" loc, PPat (pat, None)) :: attrs in
      Pat.any ~loc ~attrs ()
    else pat
 *)

  (* スケルトンのチェック *)
  let check_loc expr slice = expr.pexp_loc = slice.pexp_loc
  let check_skeleton expr = check_loc (Exp.ident skeleton) expr



  let rec to_exp exp = match exp.pexp_attributes with
      [] -> raise Not_found
    | ({txt = name}, payload) :: rest ->
       match payload with
         PStr [{pstr_desc = Pstr_eval (exp', _)}] when name = "exp" -> exp'
       | _ -> to_exp {exp with pexp_attributes = rest}

end

let skeleton' = Exp.ident Hole.skeleton

let hole_str = Hole.item
let hole_of_exp exp = Hole.hole_of_exp exp
let hole_of_pat pat = Hole.hole_of_pat pat

module Desc = struct

  (* desc 生成関数の型 *)
  type 'a make_exp_desc =
    'a list -> expression -> expression_desc
  type make_exp_desc2 =
    expression -> expression -> expression option -> expression_desc

  type 'b make_pat_desc = 'b list -> pattern -> pattern_desc

  (* open Abst *)
  let wildcard = Pat.any ()

  (* expression : expression_desc -> expression -> expression *)
  let expression pexp_desc expr = {expr with pexp_desc}

  (* pattern : pattern_desc -> pattern -> pattern *)
  let pattern ppat_desc pat = {pat with ppat_desc}

  (* to_exp :
      ('a list -> expression -> expression_desc)
    -> 'a list -> expression -> expression -> expression *)
  let to_exp fd xs e expr = expression (fd xs e) expr
  let to_exp2 fd e1 e2 eop expr = expression (fd e1 e2 eop) expr

  (* to_pat :
      ('a list -> pattern -> pattern_desc)
    -> 'a list -> pattern -> pattern -> pattern *)
  let to_pat fd ys p pat = pattern (fd ys p) pat

  (* pexp_desc の生成 *)
  let e_let flg vs e = Pexp_let (flg, vs, e)
  let e_function cs _ = Pexp_function (cs)
  let e_fun l eop p e = Pexp_fun (l, eop, p, e)
  let e_apply les e = Pexp_apply (e, les)
  let e_match cs e = Pexp_match (e, cs)
  let e_try cs e = Pexp_try (e, cs)
  let e_tuple es _ = Pexp_tuple (es)
  let e_construct lid es e =
    if es = [] then Pexp_construct (lid, Some e)
    else if e = skeleton' then Pexp_construct (lid, None)
    else Pexp_construct (lid, Some (to_exp e_tuple es e e))
  let e_variant l _ e = Pexp_variant (l, Some e)
  let e_record les e =
    if e = skeleton' then Pexp_record (les, None)
    else Pexp_record (les, Some e)
  let e_field lid _ e = Pexp_field (e, lid)
  let e_setfield lid e1 e2 = Pexp_setfield (e1, lid, e2)
  let e_array es _ = Pexp_array (es)
  let e_constraint ct _ e = Pexp_constraint (e, ct)
  let e_ifthenelse e1 e2 eop = Pexp_ifthenelse (e1, e2, eop)
  let e_sequence e1 e2 = Pexp_sequence (e1, e2)

  (* こっちを使う *)
  let enop e = if Hole.check_skeleton e then None else Some e
  let deop eop = match eop with None -> skeleton' | Some e -> e

  (* make_exp_desc *)
  let pexp_let flg vs e = Pexp_let (flg, vs, e)
  let pexp_function cs _ = Pexp_function (cs)
  let pexp_fun l eop p _ e = Pexp_fun (l, eop, p, e)
  let pexp_apply les e = Pexp_apply (e, les)
  let pexp_match cs e = Pexp_match (e, cs)
  let pexp_try cs e = Pexp_try (e, cs)
  let pexp_tuple es _ = Pexp_tuple (es)
  let pexp_construct lid _ e = Pexp_construct (lid, enop e)
  let pexp_variant l _ e = Pexp_variant (l, enop e)
  let pexp_record les e = Pexp_record (les, enop e)
  let pexp_field lid _ e = Pexp_field (e, lid)
  let pexp_array es _ = Pexp_array (es)
  let pexp_constraint ct _ e = Pexp_constraint (e, ct)
  let pexp_assert _ e = Pexp_assert (e)
  (* make_exp_desc2 *)
  let pexp_setfield lid e1 e2 _ = Pexp_setfield (e1, lid, e2)
  let pexp_ifthenelse e1 e2 eop = Pexp_ifthenelse (e1, e2, eop)
  let pexp_sequence e1 e2 _ = Pexp_sequence (e1, e2)

  (* location の比較 *)
  let comp_loc_exp e1 e2 =
    if e1 = e2 then 1 else if e1.pexp_loc = e2.pexp_loc then 0 else -1


  (* leaf の判定 *)
  let leaf_exp {pexp_desc} = match pexp_desc with
    | Pexp_ident _ | Pexp_constant _ -> true
    | Pexp_construct (_, None) | Pexp_variant (_, None) -> true
    | _ -> false

  (* 式のmap関数 *)
  (* expr と skeleton にはかけない *)
  let map_exp f expr =

    let f1 map1 fd xs e =
      {expr with
        pexp_desc =
          fd (List.map (map1 f Map.id) xs)
             (if Hole.check_skeleton e then e else f e)}

    and f2 fd e1 e2 eop =
      {expr with
        pexp_desc =
          fd (f e1) (f e2)
             (if eop = None then None else enop (f (deop eop)))} in

    if leaf_exp expr then expr
    else
      match expr.pexp_desc with
      | Pexp_let (flg, vs, e) ->
         f1 Map.v1 (pexp_let flg) vs e
      | Pexp_function (cs) ->
         f1 Map.c1 pexp_function cs skeleton'
      | Pexp_fun (l, eop, p, e) ->
         f1 Map.e1 (pexp_fun l eop p) [] e
      | Pexp_apply (e, les) -> (*
       let ls =
         if e = hole_of_exp e then
           (* dummy apply で hole の引数を残す意味はない *)
           List.filter (fun (_, en) -> en <> hole_of_exp en) les
         else les in *)
         f1 Map.le pexp_apply les e
      | Pexp_match (e, cs) ->
         f1 Map.c1 pexp_match cs e
      | Pexp_try (e, cs) ->
         f1 Map.c1 pexp_try cs e
      | Pexp_tuple (es) ->
         f1 Map.e1 pexp_tuple es skeleton'
      | Pexp_construct (lid, Some e) ->
         f1 Map.e1 (pexp_construct lid) [] e
      | Pexp_variant (l, Some e) ->
         f1 Map.e1 (pexp_variant l) [] e
      | Pexp_record (ls, eop) ->
         f1 Map.le pexp_record ls (deop eop)
      | Pexp_field (e, lid) ->
         f1 Map.e1 (pexp_field lid) [] e
      | Pexp_setfield (e1, lid, e2) ->
         f2 (pexp_setfield lid) e1 e2 None
      | Pexp_array (es) ->
         f1 Map.e1 pexp_array es skeleton'
      | Pexp_ifthenelse (e1, e2, eop) ->
         f2 pexp_ifthenelse e1 e2 eop
      | Pexp_sequence (e1, e2) ->
         f2 pexp_sequence e1 e2 None
      | Pexp_constraint (e, ct) ->
         f1 Map.e1 (pexp_constraint ct) [] e
      | Pexp_assert (e) ->
         f1 Map.e1 pexp_assert [] e
      | _ -> failwith "not supported."
                      
  (* expr にかけて再帰 *)
  let rec map_exp_all f expr =
    if leaf_exp expr then f expr
    else f (map_exp (map_exp_all f) expr)

  (* 式のfold関数 *)
  (* expr と skeleton にはかけない *)
  let fold_exp f init expr =
    let f0 e =
      if Hole.check_skeleton e then init else f init e in
    let f1 e_in_x xs e = 
      List.fold_left f (f0 e) (List.map e_in_x xs)
    and f2 e1 e2 eop = f (f (f0 (deop eop)) e2) e1 in

    if leaf_exp expr then init
    else
      match expr.pexp_desc with
      | Pexp_let (_, vs, e) -> f1 Map.e_in_v vs e
      | Pexp_function (cs) -> f1 Map.e_in_c cs skeleton'
      | Pexp_fun (_, _, _, e) -> f0 e
      | Pexp_apply (e, ls) -> f1 snd ls e
      | Pexp_match (e, cs) -> f1 Map.e_in_c cs e
      | Pexp_try (e, cs) -> f1 Map.e_in_c cs e
      | Pexp_tuple (es) -> f1 Map.id es skeleton'
      | Pexp_construct (_, Some e) -> f0 e
      | Pexp_variant (_, Some e) -> f0 e
      | Pexp_record (ls, eop) ->
         f1 snd ls (deop eop)
      | Pexp_field (e, _) -> f0 e
      | Pexp_setfield (e1, _, e2) -> f2 e1 e2 None
      | Pexp_array (es) -> f1 Map.id es skeleton'
      | Pexp_ifthenelse (e1, e2, eop) -> f2 e1 e2 eop
      | Pexp_sequence (e1, e2) -> f2 e1 e2 None
      | Pexp_constraint (e, _) -> f0 e
      | Pexp_assert (e) -> f0 e
      | _ -> init

  (* expr にかけて再帰 *)
  let rec fold_exp_all f init expr =
    if leaf_exp expr then f init expr
    else f (fold_exp (fold_exp_all f) init expr) expr


  (* ppat_desc の生成 *)
  let p_alias str _ p = Ppat_alias (p, str)
  let p_tuple ps _ = Ppat_tuple (ps)
  let p_construct lid ps p =
    if ps = [] then Ppat_construct (lid, Some p)
    else if p = wildcard then Ppat_construct (lid, None)
    else Ppat_construct (lid, Some (to_pat p_tuple ps p p))
  let p_variant l _ p = Ppat_variant (l, Some p)
  let p_record flg lps _ = Ppat_record (lps, flg)
  let p_array ps _ = Ppat_array (ps)
  let p_or p1 p2 = Ppat_or (p1, p2)
  let p_constraint ct _ p = Ppat_constraint (p, ct)

end

module Set_p = struct
  (* get int ->  expression -> int *)
  let get _ {pexp_attributes = attrs} =
    let (_, k) = List.find (function (_, Set_p _) -> true | _ -> false) attrs in 
    (match k with
     | Set_p m -> m
     | _ -> assert false)

let set' n ({pexp_attributes = attrs} as expr) =
    let attrs' =
      List.map (
          fun (lid, payload) ->
          lid, match payload with
               | Set_p m ->
                  (* sel = true : 負, sel = false : 正 *)
                  Set_p (n :: m)
               | _ -> payload
        ) attrs in
    if attrs = attrs' then
      (* 追加 *)
      Exp.attr expr (mknoloc "set", Set_p [n])
    else
      (* 上書き *)
      {expr with pexp_attributes = attrs'}

  (* size を set する *)
 (* let rec set expr =
    if Desc.leaf_exp expr then
      (* 子ノードなし *)
      set' 1 expr
    else
      (* 子ノードあり *)
      let expr' = Desc.map_exp set expr in
      let n = Desc.fold_exp get expr' in
      set' n expr' *)
end
  

module Size = struct

  let set_size = true
  let set_resize = true

  (* size を求める関数 *)
  let get' n (_, payload) = match payload with
      Size m -> m + n | _ -> n
  (* get int ->  expression -> int *)
  let get n {pexp_attributes = attrs} =
    List.fold_left get' n attrs

  (* 比較関数 *)
  (* comp1 : e の size と 1 を比較 *)
  let comp1 e = compare (get 0 e) 1

  (* is1 : sizeが1でtrue *)
  let is1 e = comp1 e = 0

  (* fltr1 : size が2以上 *)
  let fltr1 e = 1 = comp1 e

  (* fltr0 : sizeが1以上でtrue *)
  let fltr0 e = 0 <= comp1 e

  (* comp2 : e1 と e2 の、m までの距離を比較 *)
  let comp2 m e1 e2 =
    if comp1 e1 < 0 then 1
    else if comp1 e2 < 0 then -1
    else
      let get_dist e = abs (m - get 0 e) in
      compare (get_dist e1) (get_dist e2)

  let get_one e = get 0 e

  (* ある式のサイズをセットする *)
  let set' ?(sel = false) n ({pexp_attributes = attrs} as expr) =
    let attrs' =
      List.map (
          fun (lid, payload) ->
          lid, match payload with
               | Size m ->
                  (* sel = true : 負, sel = false : 正 *)
                  Size (abs m |> if sel then (-) n else (+) n)
               | _ -> payload
        ) attrs in
    if attrs = attrs' then
      (* 追加 *)
      Exp.attr expr (mknoloc "size", Size n)
    else
      (* 上書き *)
      {expr with pexp_attributes = attrs'}

  (* size を set する *)
  let rec set expr =
    if Desc.leaf_exp expr then
      (* 子ノードなし *)
      set' 1 expr
    else
      (* 子ノードあり *)
      let expr' = Desc.map_exp set expr in
      let n = Desc.fold_exp get 1 expr' in
      set' n expr'

  (* reset' : expr の size を n にする *)
  let reset' n expr =
    {expr with
      pexp_attributes =
        List.map (
            fun (lid, payload) ->
            (lid, match payload with
                  | Size _ -> Size n
                  | _ -> payload)) expr.pexp_attributes}
  let reset expr = reset' 0 expr
  let reset1 x expr =
    reset' (get (x 0 1) expr) expr

  let rec resize expr =

    if Desc.leaf_exp expr then expr

    else
      (* 未確定の子ノード *)
      let children =
        Desc.fold_exp
          (fun es e -> if fltr0 e then e :: es else es) [] expr in
      match children with
        [] -> reset expr
      | first :: rest ->
         let map f = Desc.map_exp f expr in
         let (n, expr') =
           if rest = [] then
             let e' = resize first in
             (get_one e', map (fun e -> if first = e then e' else e))
           else
             let expr'' =
               map (fun e -> if List.mem e children then resize e else e) in
             (Desc.fold_exp get 1 expr'', expr'') in
         reset' n expr'

  (* 確定させる *)
  let terminated expr = set' ~sel:true 0 expr

  (* terminated check *)
  (* すべての式が terminated であれば true *)
  let check' init expr = init && not (fltr0 expr)
  let check expr = Desc.fold_exp_all check' true expr

  (* 子ノード *)
  let children expr =
    (* expr の半分に近いノードから昇順にソート *)
    let children' =
      Desc.fold_exp (
          fun acc exp ->
          acc @ if fltr0 exp then [exp] else []) [] expr in
    let comp' = comp2 ((get 2 expr) / 2) in

    (* ソート *)
    List.sort comp' children'

  let term_hole e = terminated (hole_of_exp e)
  let get_childNoResize expr =

    (* 式exprのサイズ *)
    let n = get_one expr in

    if n = 1 then
      (expr, Map.id, term_hole)

    else

    (* 比較関数 *)
    let comp_child exp' exp =
      if fltr0 exp && comp2 (n / 2) exp' exp >= 0 then exp else exp' in

    let expr_cxt_one e' =
      Desc.map_exp_all (
          fun e ->
          if e = e' then term_hole e
          else if Hole.check_loc e e' then e'
          else e
        ) expr in


    let rec get_childNoResize' expr_cxt_expect expr' =
      let child = Desc.fold_exp comp_child expr' expr' in
      if child = expr' then
        (expr', expr_cxt_expect, expr_cxt_one)
      else
        let expr_cxt_expect' e' =
          expr_cxt_expect (
              Desc.map_exp (
                  fun e ->
                  if Hole.check_loc e e'
                  then e'
                  else if fltr0 e then term_hole e
                  else e) expr') in
        get_childNoResize' expr_cxt_expect' child in

    get_childNoResize' Map.id expr

  let reset_hole e = reset (hole_of_exp e)

  let get_childWithResize expr =

    let n = get_one expr in

    if Desc.leaf_exp expr then
      (* 子ノードなし *)
      (expr, reset_hole, reset_hole)

    else
      let comp_child exp' exp =
        if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in
      let rec get_childWithResize' expr_cxt_expect expr' =
        let child = Desc.fold_exp comp_child expr' expr' in
        if child = expr' then
          let expr_cxt_one e' =
            let slice =
              Desc.map_exp_all (
                  fun e ->
                  if e = e' then reset_hole e
                  else if Hole.check_loc e e' then e' else e
                ) expr in
            resize slice in
          (expr', expr_cxt_one, expr_cxt_expect)
        else
          let expr_cxt_expect' e' =
            let n = get_one e' in
            let slice = match expr'.pexp_desc with
              | Pexp_apply (e, les) when Hole.check_loc e e' && n = 1 ->
                 let les' =
                   List.map (
                       fun (ln, en) ->
                       (ln, if fltr0 en then reset_hole e else e)
                     ) les in
                 {expr' with pexp_desc = Pexp_apply (e', les')} |> reset
              | _ ->
                 Desc.map_exp (
                     fun e ->
                      if Hole.check_loc e e' then e'
                      else if fltr0 e then reset_hole e
                      else e
                   ) expr' |> reset' n in
            expr_cxt_expect slice in

(*
          let expr_cxt_expect' e' =
            expr_cxt_expect (
                (* 位置情報が一致した場合、式を差し替える *)
                Desc.map_exp (
                    fun e ->
                    if Hole.check_loc e e' then e'
                    else if fltr0 e then reset_hole e
                    else e
                  ) expr'
                (* 式のサイズは e' と同じになる *)
                |> reset' (get_one e')) in
 *)
          get_childWithResize' expr_cxt_expect' child in

      get_childWithResize' Map.id expr

  let expect expr' e' =
    Desc.map_exp (
        fun e ->
        if Hole.check_loc e e' then e'
        else if fltr0 e then reset_hole e
        else e) expr'

  let getChild _ getChild' expr_cxt_expect expr =

    if Desc.leaf_exp expr then
      (expr, reset, reset_hole)

    else

      (* 今まで：消すものを探索してからresizeしていた *)
(*
      let expr_cxt_one e' =
        (* sel = true で resize する *)
        Desc.map_exp_all (
            fun e ->
            if e = e' then reset_hole e
            else if Hole.check_loc e e' then e' else e
          ) expr |> if sel then resize else Map.id in
 *)
      (* これから：探索とresize を同時に行う *)
      let expr_cxt_one e =
        let open Location in
        let rec expr_cxt_one' e' =
          (* 式のサイズ *)
          let n = ref 1 in
          let expr' =
            Desc.map_exp (
                fun e'' ->
                if e = e'' then reset_hole e''
                else
                  let expr'' =
                    if e.pexp_loc = e''.pexp_loc then e
                    else if
                      e.pexp_loc.loc_end < e''.pexp_loc.loc_start
                      || e''.pexp_loc.loc_end < e.pexp_loc.loc_start then e''
                    else
                      expr_cxt_one' e'' in
                  n := get !n expr''; expr''
              ) e' in
          if !n = 1 then n := 0;
          reset' !n expr' in
        expr_cxt_one' expr in

      getChild' expr_cxt_expect expr_cxt_one expr

  (* slicing2 *)

(*
  let getChild2 expr =

    let n = get_one expr in
    let comp_child exp' exp =
      if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in

    let getChild' expr_cxt_expect expr_cxt_one expr' =
      (Desc.fold_exp comp_child expr' expr', expr_cxt_expect, expr_cxt_one) in

    getChild false getChild' (expect expr) expr
 *)



  (* child の選択を最大サイズに変更したバージョンを別で追加 *)

(*
  let getChildSet expr =

    let n = get_one expr in

(*
    let comp exp' exp =
      if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in
 *)
    let open Location in

    let rec getChildSet' (expr', abst') =

      (* 最大サイズの選択バージョン *)
      let comp e' e =
        let n' = get_one e' and init = e' = expr' in
        if init && n' < n / 2 then e'
        else if init && fltr0 e then e
        else if n' < get_one e then e else e' in

      let child = Desc.fold_exp comp expr' expr' in

      if child = expr' then
        (expr', fun sel expr_cxt e -> expr_cxt (abst' sel e))

      else
        match expr'.pexp_desc with

        | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as en)) ->
           let child'' = List.fold_left comp skeleton' es in

           if child'' = skeleton' then
             (expr', fun sel expr_cxt e -> expr_cxt (abst' sel e))

           else
             let abst sel e =
               let m = ref 1 in
               let set' e' = m := get !m e'; e' in
               let expr'' =
                 let en' =
                   Desc.map_exp (
                       fun e' ->
                       if e = e' then
                         if sel then set' e' else reset_hole e'
                       else if e.pexp_loc = e'.pexp_loc then
                         set' e
                       else if
                         e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                         || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                         if sel then reset_hole e' else set' e'
                       else
                         set' e'
                     ) en in
                 if !m = 1 then m := 0;
                 {expr' with
                   pexp_desc =
                     Pexp_construct (lid, Some (reset' !m en'))} in
               if 0 < !m then m := !m + 1;
               abst' sel (reset' !m expr'') in

             getChildSet' (child'', abst)

        | _ ->
           (* construct の場合分けを追加する *)
           let abst sel e =
             let m = ref 1 in
             let set' e' = m := get !m e'; e' in
             let expr'' =
               Desc.map_exp (
                   fun e' ->
                   if e = e' then
                     if sel then set' e' else reset_hole e'
                   else if e.pexp_loc = e'.pexp_loc then
                     set' e
                   else if
                     e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                     || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                     if sel then reset_hole e' else set' e'
                   else
                     set' e'
                 ) expr' in
             if !m = 1 then m := 0;
             abst' sel (reset' !m expr'') in

           getChildSet' (child, abst) in

    getChildSet' (expr, fun _ e -> e)
*)



(*
  let rec getChildSet' n (expr', abst') =
    let open Location in

    (* 元のやつ *)
    (* 比較関数：comp2 n *)
(*
    let comp e' e =
      if 0 <= comp2 n e' e && fltr0 e then e else e' in
    let child = Desc.fold_exp comp expr' expr' in
 *)

(*
    let comp c1 c2 e' e =
      if c1 e' e then
        if fltr0 e then e else e'
      else
        if c2 e' e then e else e' in
    let getChild fltr child =
      if fltr child then child else Desc.fold_exp comp child child


    let comp e' e =
      if 0 <= comp2 n e' e then
        if fltr0 then e else e'
      else
        e' in

    let comp e' e =
      if e' = expr' then
        if fltr0 e then e else e'
      else
        if get_one e' < get_one e then e else e' in


 *)


    (* 単純なサイズの大きさで比較 *)
    let comp e' e =
      if e' = expr' then
        if fltr0 e then e else e'
      else
        if get_one e' < get_one e then e else e' in

    let child =
      if get_one expr' < n then expr'
      else
        Desc.fold_exp comp expr' expr' in

    if child = expr' then
      (expr', fun sel expr_cxt e -> expr_cxt (abst' sel e))

    else
      match expr'.pexp_desc with
        
      | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as en)) ->
         let child'' = List.fold_left comp skeleton' es in
         
         if child'' = skeleton' then
           (expr', fun sel expr_cxt e -> expr_cxt (abst' sel e))

         else
           let abst sel e =
             let m = ref 1 in
             let set' e' = m := get !m e'; e' in
             let expr'' =
               let en' =
                 Desc.map_exp (
                     fun e' ->
                     if e = e' then
                       if sel then set' e' else reset_hole e'
                     else if e.pexp_loc = e'.pexp_loc then
                       set' e
                     else if
                       e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                       || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                       if sel then reset_hole e' else set' e'
                     else
                       set' e'
                   ) en in
               if !m = 1 then m := 0;
               {expr' with
                 pexp_desc =
                   Pexp_construct (lid, Some (reset' !m en'))} in
             if 0 < !m then m := !m + 1;
             abst' sel (reset' !m expr'') in
           getChildSet' n (child'', abst)
                        
      | _ ->
         (* construct の場合分けを追加する *)
         let abst sel e =
           let m = ref 1 in
           let set' e' = m := get !m e'; e' in
           let expr'' =
             Desc.map_exp (
                 fun e' ->
                 if e = e' then
                   if sel then set' e' else reset_hole e'
                 else if e.pexp_loc = e'.pexp_loc then
                   set' e
                 else if
                   e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                   || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                   if sel then reset_hole e' else set' e'
                 else
                   set' e'
               ) expr' in
           if !m = 1 then m := 0;
           abst' sel (reset' !m expr'') in
         getChildSet' n (child, abst)
 *)


  let rec getChildSet' fltr3 fltr2 fltr' (expr', abst') =
    let open Location in

    let return () =
      (expr', fun sel expr_cxt e -> expr_cxt (abst' sel e)) in

    if fltr' expr' then
      return ()
    else
      let comp e' e =
        if fltr3 expr' e' e then
          if fltr0 e then e else e'
        else
          if fltr2 e' e then e else e' in
      let child = Desc.fold_exp comp expr' expr' in
      if child = expr' then
        return ()
      else
        match expr'.pexp_desc with
        
        | Pexp_construct (lid, Some ({pexp_desc = Pexp_tuple es} as en)) ->
           let child'' = List.fold_left comp skeleton' es in
           if child'' = skeleton' then
             return ()
           else
             let abst sel e =
               let m = ref 1 in
               let set' e' = m := get !m e'; e' in
               let expr'' =
                 let en' =
                   Desc.map_exp (
                       fun e' ->
                       if e = e' then
                         if sel then set' e' else reset_hole e'
                       else if e.pexp_loc = e'.pexp_loc then
                         set' e
                       else if
                         e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                         || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                         if sel then reset_hole e' else set' e'
                       else
                         set' e'
                     ) en in
                 if !m = 1 then m := 0;
                 {expr' with
                   pexp_desc =
                     Pexp_construct (lid, Some (reset' !m en'))} in
               if 0 < !m then m := !m + 1;
               abst' sel (reset' !m expr'') in
             getChildSet' fltr3 fltr2 fltr' (child'', abst)
                          
        | _ ->
           (* construct の場合分けを追加する *)
           let abst sel e =
             let m = ref 1 in
             let set' e' = m := get !m e'; e' in
             let expr'' =
               Desc.map_exp (
                   fun e' ->
                   if e = e' then
                     if sel then set' e' else reset_hole e'
                   else if e.pexp_loc = e'.pexp_loc then
                     set' e
                   else if
                     e.pexp_loc.loc_end < e'.pexp_loc.loc_start
                     || e'.pexp_loc.loc_end < e.pexp_loc.loc_start then
                     if sel then reset_hole e' else set' e'
                   else
                     set' e'
                 ) expr' in
             if !m = 1 then m := 0;
             abst' sel (reset' !m expr'') in
           getChildSet' fltr3 fltr2 fltr' (child, abst)

  let getChildSet expr =

    let n = get_one expr / 2 in
    let fltr3 expr' e' _ = expr' = e'
    and fltr2 e' e = get_one e' < get_one e
    and fltr' expr' = get_one expr' < n in
    getChildSet' fltr3 fltr2 fltr' (expr, fun _ e -> e)

  let getChildSet2 expr =
    let n = get_one expr / 2 in
    let fltr3 _ e' e = 0 <= comp2 n e' e
    and fltr2 _ _ = false
    and fltr' _ = false in
    getChildSet' fltr3 fltr2 fltr' (expr, fun _ e -> e)

  (* resize あり *)
  let getChild2 expr =

    let n = get_one expr in
    let comp_child exp' exp =
      if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in

    let rec getChild' expr_cxt_expect expr_cxt_one expr' =
      
      let child = Desc.fold_exp comp_child expr' expr' in

      if child = expr' then
        (expr', expr_cxt_expect, expr_cxt_one)

      else
        match expr'.pexp_desc with

        | Pexp_construct (lid, Some {pexp_desc = Pexp_tuple es}) ->

           let child' =
             List.fold_left comp_child (reset child) es in
           if child' = reset child then
             (expr', expr_cxt_expect, expr_cxt_one)

           else
             let expr_cxt_expect' e' =
               {expr' with
                 pexp_desc =
                   Pexp_construct (lid, Some (expect child e'))
               } |> expr_cxt_expect |> reset' (get_one e') in
             getChild' expr_cxt_expect' expr_cxt_one child'

        | _ ->
           let expr_cxt_expect' e' =
             expect expr' e' |> expr_cxt_expect |> reset' (get_one e') in
           getChild' expr_cxt_expect' expr_cxt_one child in

    getChild true getChild' resize expr



  (* slicing3 *)

(*
  let getChild3 expr =

    let n = get_one expr in
    let comp_child exp' exp = match exp'.pexp_desc with
      | Pexp_fun _ when fltr1 exp' -> exp'
      | Pexp_let _ when fltr1 exp' -> exp'
      | Pexp_construct (_, Some {pexp_desc = Pexp_tuple _})
           when fltr1 exp' -> exp'
      | _ ->
         if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in

    let rec getChild' expr_cxt_expect expr_cxt_one expr' =

      let child = Desc.fold_exp comp_child expr' expr' in
      
      if child = expr' then
        (expr', expr_cxt_expect, expr_cxt_one)
          
      else
        let expr_cxt_expect' e' =
          expect expr' e' |> expr_cxt_expect |> reset' (get_one e') in
        getChild' expr_cxt_expect' expr_cxt_one child in

    getChild true getChild' Map.id expr
 *)


  let getChild3 expr =

    let n = get_one expr in

    let rec resize expr =

      if Desc.leaf_exp expr || get 0 expr = 0 then expr

      else if fltr0 expr then
        let expr' = Desc.map_exp resize expr in
        reset' (Desc.fold_exp get 1 expr') expr'

      else
        let children =
          Desc.fold_exp (
              fun acc e ->
              if hole_of_exp e = e then acc else e :: acc
            ) [] expr in

        match expr.pexp_desc with

        | Pexp_apply (e, les) when children = [] ->

           reset_hole
             {expr with
               pexp_desc =
                 Pexp_apply
                   (Hole.to_exp e,
                    List.map (
                        fun (l', e') -> (l', Hole.to_exp e')
                      ) les)}

         | _ ->
            reset expr



(*
        let children =
          Desc.fold_exp (
              fun acc e ->
              if hole_of_exp e = e then acc else e :: acc
            ) [] expr in

        if children <> [] then
          reset expr

        else
          match expr.pexp_desc with

          | Pexp_let (flg, vs, e) ->
             reset_hole
               {expr with
                 pexp_desc =
                   Pexp_let
                     (flg,
                      List.map (Map.v1 Hole.to_exp Map.id) vs,
                      Hole.to_exp e)}

          | Pexp_apply (e, les) ->

             reset_hole
               {expr with
                 pexp_desc =
                   Pexp_apply
                     (Hole.to_exp e,
                      List.map (
                        fun (l', e') -> (l', Hole.to_exp e')
                        ) les)}

          | Pexp_ifthenelse (e1, e2, eop)  ->

             reset_hole
               {expr with
                 pexp_desc =
                   Pexp_ifthenelse
                     (Hole.to_exp e1,
                      Hole.to_exp e2,
                      match eop with
                      | None -> None
                      | Some e3 -> Some (Hole.to_exp e3))}

          | _ -> reset expr in
 *) in

    let expect' expr_cxt_expect expr' e' =
      expect expr' e' |> expr_cxt_expect in

    let comp_child exp' exp =
      if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp'

    and expr_cxt_one e' =
      let slice =
        Desc.map_exp_all (
            fun e ->
            if e = e' then reset_hole e
            else if Hole.check_loc e e' then e' else e
          ) expr in
      resize slice in

    let rec getChild' expr_cxt_expect expr' =

      let child = Desc.fold_exp comp_child expr' expr' in

      if child = expr' then
        (expr', expr_cxt_expect, expr_cxt_one)

      else
        match expr'.pexp_desc with

        | Pexp_fun _ when (
          match child.pexp_desc with
          | Pexp_fun _ -> true
          | _ -> false) ->
           (* fun文 *)
           (child, expect' expr_cxt_expect expr', expr_cxt_one)

        | Pexp_let (_, vs, _) when (
          match child.pexp_desc with
          | Pexp_fun _ -> List.exists (fun {pvb_expr} -> pvb_expr = child) vs
          | _ -> false) ->
           (* let文 *)
           (child, expect' expr_cxt_expect expr', expr_cxt_one)

        | Pexp_construct (lid, Some {pexp_desc = Pexp_tuple es}) ->
           (* construct *)

           let child' =
             List.fold_left comp_child child es in
           if child' = child then
             (expr', expr_cxt_expect, expr_cxt_one)
           else
             let expr_cxt_expect' e' =
               {expr' with
                 pexp_desc =
                   Pexp_construct (lid, Some (expect child e'))
               } |> expr_cxt_expect in
             getChild' expr_cxt_expect' child'

        | _ ->
           getChild' (expect' expr_cxt_expect expr') child in

    getChild' resize expr


(*

  let getChild3 expr =

    if Desc.leaf_exp expr then
      (expr, reset, reset_hole)

    else
      let n = get_one expr in

      let comp_child exp' exp = match exp'.pexp_desc with
        | Pexp_fun _ when fltr1 exp' -> exp'
        | Pexp_let _ when fltr1 exp' -> exp'
        | Pexp_construct (_, Some {pexp_desc = Pexp_tuple _})
             when fltr1 exp' -> exp'
        | _ ->
           if 0 <= comp2 (n / 2) exp' exp && fltr0 exp then exp else exp' in

      let expr_cxt_one e' =
        Desc.map_exp_all (
            fun e ->
            if e = e' then reset_hole e
            else if Hole.check_loc e e' then e' else e
          ) expr |> resize in


      let rec getChild3' expr_cxt_expect expr' =

        let child = Desc.fold_exp comp_child expr' expr' in

        if child = expr' then
          (expr', expr_cxt_expect, expr_cxt_one)

        else
          let expr_cxt_expect' e' =
            expect expr' e' |> expr_cxt_expect |> resize in
          getChild3' expr_cxt_expect' child in

      getChild3' Map.id expr
 *)


  (* get_child : expression -> expression * (expression -> expression) *)
  (* 式 expr のサイズ n の半分に最も近い子ノードを探す *)

  let get_child =
    if set_resize then get_childWithResize else get_childNoResize


  (* get_child *)
  (* pexp_apply:
       子ノードに未確定なしだった場合、関数部分で強制終了
   *)

  (* pexp_let, pexp_fun, pexp_construct (tuple element) : 現れた時点でchild に確定。 *)


  (* size を与える関数 *)
  (* set_one : ?n:int -> expression -> expression *)
  let set_one ?(n = 1) slice =
    if set_size then
      Exp.attr slice (mknoloc "size", Size n)
    else slice

  (* set_all : ('a list -> 'a list -> expression ->
                 ('a list -> expression -> expression_desc) -> expression)
                -> ('a list -> expression -> expression_desc)
                -> ('a -> expression) -> 'a list -> expression
                -> expression *)
  let set_all fp fd fx acc s_all =
    if set_size then
      let n = List.fold_left
                (fun n x -> get n (fx x))
                (get 1 s_all) acc in
      set_one ~n (fp acc [] s_all fd)
    else (fp acc [] s_all fd)

(*
  let rec set expr =

    let set_one n desc =
      set_one ~n (Desc.expression desc expr) in

    let set_all ?(e = skeleton') map1 fx fd xs =
      (* サイズを求めつつリスト部分を更新 *)
      let e' = set e in
      let (n, xs') =
        List.fold_left
          (fun (n, acc) x ->
            let en' = set (fx x) in
            (get n en', acc @ [Map.set_exp map1 x en'])
          ) (get 1 e', []) xs in
      set_one n (fd xs' e') in

    match expr.pexp_desc with
    (* とりあえず let sum x y = x + y in sum 1 2.でチェックする用に *)

    | Pexp_let (flg, vs, e) ->
       set_all ~e Map.v1 (fun v -> v.pvb_expr) (Desc.e_let flg) vs

    | Pexp_apply (e, les) ->
       set_all ~e Map.le snd Desc.e_apply les

    | Pexp_fun (l, eop, p, e) ->
       let e' = set e in
       set_one (get 1 e') (Desc.e_fun l eop p e')

    | d -> set_one 1 d
 *)

  let compare_size m e1 e2 =
    compare (abs (m - get 0 e1)) (abs (m - get 0 e2))
(*
  let half_size_child m es e =
    List.fold_left (
        fun e1 e2 ->
        if 0 < compare_size m e1 e2 then e2 else e1
      ) e es
 *)
  (* 親ノードのサイズを取得して、子ノードの式を半分に近い順に並び替える *)
  let node_sort expr =

    let m = (get 2 expr) / 2 in (* 親のサイズの半分 *)
    let sort_size es = List.stable_sort (compare_size m) es in

    match expr.pexp_desc with
    | Pexp_ident _ | Pexp_constant _ -> sort_size [expr]

    | Pexp_let (_, vs, e) ->
       sort_size (e :: List.map (fun v -> v.pvb_expr) vs)
    | Pexp_function (cs) ->
       sort_size (List.map (fun c -> c.pc_rhs) cs)
    | Pexp_fun (_, eop, _, e) ->
       sort_size (match eop with None -> [e] | Some e' ->[e; e'])
    | Pexp_apply (e, les) ->
       sort_size (e :: List.map snd les)
    | Pexp_match (e, cs) ->
       sort_size (e :: List.map (fun c -> c.pc_rhs) cs)
    | Pexp_try (e, cs) ->
       sort_size (e :: List.map (fun c -> c.pc_rhs) cs)
    | Pexp_tuple (es) -> sort_size es
    | Pexp_construct (_, Some {pexp_desc = Pexp_tuple es}) -> sort_size es
    | Pexp_construct (_, Some e) -> [e]
    | Pexp_variant (_, Some e) -> [e]
    | Pexp_record (les, eop) ->
       sort_size ((List.map snd les)
                  @ match eop with None -> [] | Some e -> [e])
    | Pexp_field (e, _) -> [e]
    | Pexp_setfield (e1, _, e2) -> sort_size [e1; e2]
    | Pexp_array (es) -> sort_size es
    | Pexp_ifthenelse (e1, e2, eop) ->
       sort_size (e1 :: e2
                  :: match eop with None -> [] | Some e3 -> [e3])
    | Pexp_sequence (e1, e2) -> sort_size [e1; e2]
    | Pexp_constraint (e, _) -> [e]
    | Pexp_send (e, _) -> [e] 
    | _ -> []

end

module Abst = struct

  let hole_of_x map1 x = map1 hole_of_exp Map.id x

  (* set_one : slice -> slice list *)
  (* 部分的に抽象化 *)
  let set_one exp =

    let sn n en sel = if sel = n then hole_of_exp en else en in

    (* リストが構文中にない場合 *)
    (* e が □ でなければ exp の desc を置き換えた要素を abst に追加 *)
    let set_some e ?(abst = []) desc =
      
      if e = hole_of_exp e then abst
      else abst @ [Desc.expression desc exp] in

    (* リストが構文中にある場合 *)
    (* 再帰で要素をひとつひとつ抽象化 *)
    let set_one' ?(es = []) ?(e = skeleton') map1 fd xs =
     
      let to_exp fd e xs = Desc.to_exp fd xs e exp in
      let fde acc = List.map (to_exp fd e) (List.rev acc) in
      let dummy_apply es =
        Desc.e_apply (List.map (fun e -> (Nolabel, e)) es) skeleton' in
      let rec set_some' acc forward backword = match backword with
       | [] -> fde acc
       | tar :: backword' ->
          (* チェック済 *)
          let forward' = forward @ [tar] in
          (* tar を□で置き換えることを試みる *)
          let dummy = hole_of_x map1  tar in
          let acc' =
            if tar = dummy then acc
            else (forward @ (dummy :: backword')) :: acc in
          set_some' acc' forward' backword' in

      set_some
        e ~abst:(set_some' [] [] xs)
        (if es = [] then fd xs (hole_of_exp e) else dummy_apply es) in
    
    (* abst_one のメイン部分 *)
    match exp.pexp_desc with

    | Pexp_let (flg, vs, e) ->
       (* let 文 *)
       (* let x = S1 in S2 => [let x = □ in S2; let x = S1 in □] *)
       set_one' ~e Map.v1 (Desc.e_let flg) vs

    | Pexp_apply (e, les) ->
       (* 関数適用 *)
       (* @ S1 .. Sn => [=@ S1..Sn; @ □..Sn; ...; @ S1..□]  *)
       set_one' ~e Map.le Desc.e_apply les

    | Pexp_function (cs) ->
       (* function *)
       (* function P1 -> S1 | ... | Pn -> Sn =>
       [function P1 -> □ | ... ; function ... | Pn -> □] *)
       set_one' Map.c1 Desc.e_function cs

    | Pexp_fun (l, eop, p, e) ->
       (* fun *)
       (* λx.S => λx.□ *)
      set_one' ~e Map.e1 (fun _ e -> Desc.e_fun l eop p e) []

    | Pexp_match (e, cs) ->
       (* match 文 *)
       (* パターンする式と結果のみを対象にしている *)
       (* match S0 with P1 -> S1 | ... | Pn -> Sn =>
       [match □ with ...; ... with P1 -> □ | ...; ... with ... | Pn -> □] *)
       set_one' ~e Map.c1 Desc.e_match cs
                
    | Pexp_try (e, cs) ->
       (* try 文 *)
       (* パターンする式と結果のみを対象にしている *)
       (* try S0 with P1 -> S1 | ... | Pn -> Sn =>
       [try □ with ...; ... with P1 -> □ | ...; ... with ... | Pn -> □] *)
       set_one' ~e Map.c1 Desc.e_try cs
                
    | Pexp_tuple (es) ->
       (* tuple *)
       (* (S1, ... Sn) => [(□, ... Sn); ... ; (S1, ..., □); @= S1 ,..., Sn] *)
       set_one' ~es Map.e1 Desc.e_tuple es
                
    | Pexp_construct (lid, Some (e)) ->
       (* コンストラクタ *)
       (* 引数が単数か複数かで分岐 *)
       let es = match e.pexp_desc with
           Pexp_tuple es -> es
         | _ -> [] in
       set_one' ~es ~e Map.e1 (Desc.e_construct lid) es
                
    | Pexp_record (les, eop) ->
       (* record *)
       (* 各フィールドを対象にしている *)
       set_one'
         ~e:(match eop with None -> skeleton' | Some e -> e)
         Map.le Desc.e_record les
         
    | Pexp_field (e, lid) ->
       set_one' ~e Map.e1 (Desc.e_field lid) []

    | Pexp_setfield (e1, lid, e2) ->
       let fd sel = Desc.e_setfield lid (sn 1 e1 sel) (sn 2 e2 sel) in
       set_some ~abst:(set_some e1 (fd 1)) e2 (fd 2)

    | Pexp_array (es) ->
       (* array *)
       set_one' ~es Map.e1 Desc.e_array es
                
    | Pexp_ifthenelse (e1, e2, eop) ->
       (* ifthenelse *)
       (* [if □ then e2 else e3;
          if e1 then □ else e3;
          if e1 then e2 else □] *)
      let e3 = match eop with
          Some e -> e | None -> skeleton' in
      let fd sel = Desc.e_ifthenelse
                     (sn 1 e1 sel) (sn 2 e2 sel)
                     (if eop <> None && sel = 3
                      then Some (hole_of_exp e3) else eop) in
      set_some
        ~abst:(set_some ~abst:(set_some e1 (fd 1)) e2 (fd 2)) e3 (fd 3)

   | Pexp_sequence (e1, e2) ->
      let fd sel = Desc.e_sequence (sn 1 e1 sel) (sn 2 e2 sel) in
      set_some ~abst:(set_some e1 (fd 1)) e2 (fd 2)

   | Pexp_constraint (e, c) ->
      (* constraint *)
      (* [(□ : c)] *)
      set_one' ~e Map.e1 (Desc.e_constraint c) []

   | _ -> if exp = hole_of_exp exp then [] else [hole_of_exp exp]

  (* 部分式を全て抽象化 *)
  let set_all exp =

    let set_all' ?(e = skeleton') map1 fd xs =
      Desc.to_exp fd (List.map (hole_of_x map1) xs) (hole_of_exp e) exp in
    let set_all'' desc = Desc.expression desc exp in 

    match exp.pexp_desc with

    | Pexp_let (flg, vs, e) ->
       set_all' ~e Map.v1 (Desc.e_let flg) vs

    | Pexp_apply (e, les) ->
       set_all' ~e Map.le Desc.e_apply les

    | Pexp_function (cs) ->
       set_all' Map.c1 Desc.e_function cs

    | Pexp_fun (l, eop, p, e) ->
       set_all'' (Desc.e_fun l eop p (hole_of_exp e))

    | Pexp_match (e, cs) ->
       set_all' ~e Map.c1 Desc.e_match cs

    | Pexp_try (e, cs) ->
       set_all' ~e Map.c1 Desc.e_try cs

    | Pexp_tuple (es) ->
       set_all' Map.e1 Desc.e_tuple es

    | Pexp_construct (lid, Some e) ->
       let es = match e.pexp_desc with
           Pexp_tuple es -> es | _ -> [] in
       set_all' ~e Map.e1 (Desc.e_construct lid) es

    | Pexp_record (les, eop) ->
       set_all' ~e:(match eop with None -> skeleton' | Some e -> e)
                Map.le Desc.e_record les

    | Pexp_field (e, lid) ->
       set_all' ~e Map.e1 (Desc.e_field lid) []

    | Pexp_array (es) ->
       set_all' Map.e1 Desc.e_array es

    | Pexp_ifthenelse (e1, e2, eop) ->
       set_all'' (
           Desc.e_ifthenelse (hole_of_exp e1)
                             (hole_of_exp e2)
                             (match eop with Some e3 -> Some (hole_of_exp e3)
                                           | None -> None))

    | Pexp_sequence (e1, e2) ->
       set_all'' (
           Desc.e_sequence (hole_of_exp e1)
                           (hole_of_exp e2))

    | Pexp_constraint (e, ct) ->
       set_all' ~e Map.e1 (Desc.e_constraint ct) []

    | d -> set_all'' d

  (* Abst.one, Abst.all *)

  let one expr =
    (* 既に確定している場合は抽象化しない *)
    if Size.fltr0 expr then Size.terminated (hole_of_exp expr) else expr

  let all expr = Size.terminated (Desc.map_exp one expr)

  let set slice expr =
    if Hole.check_loc slice expr then slice else expr

  let get' sel slice expr =

    if Hole.check_loc slice expr = sel then
      (* sel = true : loc = true *)
      (* sel = false : loc = false *)
      (* expr を抽象化 *)
      one expr
    else
      set slice expr

  (* Abst.get *)
  let get expr sel slice =
    (if Hole.check_skeleton slice then
       if sel then Size.terminated else all
     else
       Desc.map_exp (
           (if Size.comp1 slice < 0 then set else get' sel)
             slice)) expr


  let exp e =
    if Size.fltr0 e then
      (hole_of_exp e)
      |> (if Size.set_resize then Size.reset else Size.terminated)
    else e;

end


(* デバッグ用 *)
module Meta = struct
  (* 型デバッガが訪れるノード数カウント用の変数 (debug_main.ml) *)

  let print_node_count =
    false (* ノード数をカウントするときには true にする *)
  (* true にすると型デバッグはできなくなる *)

  let print_asked_expr =
    false (* カウントされた質問を表示するときには true にする *)
  (* スライス表示用変数 (debug_slice.ml) *)

  let print_slice =
    not print_node_count && (* ノード数カウント中はスライスを表示しない *)
      false (* スライス結果を表示するときに true にする *)
        
  (* OCaml のエラーメッセージ Errors.report_error 制御用変数
   (toplevel/toploop.ml, driver/compile.ml) *)
        
  let print_ocaml_error =
    not print_node_count && (* ノード数カウント中は表示しない *)
      true  (* OCaml のエラーメッセージを消すときに false にする *)

  (* スライスをするかどうかを制御する変数
   (debug_slice.ml, debug_main.ml) *)     
  let on_exp_slice =
    print_node_count || (* ノード数カウント中はスライスを行う *)
      true (* スライスをしないときには false を代入する *)
        
  let on_pat_slice =
    ref false (* パターンのスライスをしないときには false を代入する *)

  let visible = false

  let clean' name expr =
    {expr with
      pexp_attributes =
        if name = "all" then [] (* 全部消す *)
        else
          List.filter (
              fun ({txt = name'}, _) ->
              name <> name'
            ) expr.pexp_attributes}

  let clean name expr =
    Desc.map_exp_all (clean' name) expr


  let rec attribute ppf (kind, attrs) = match attrs with
      [] -> ()
    | ({txt = s}, PStr [{pstr_desc = Pstr_eval (e, _)}]) :: _ when s = kind ->
       (* 式のホール □ *)
       if visible then Format.fprintf ppf "【%a】" Pprintast.expression e
       else Format.fprintf ppf "□"
    | ({txt = s}, PPat (p, _)) :: _ when s = kind ->
       (* パターンのホール ■ *)
       if visible then Format.fprintf ppf "【%a】" Pprintast.pattern p
       else Format.fprintf ppf "■"
    | ({txt = s}, Size n) :: _ when s = kind ->
       (* サイズ *)
       Format.fprintf ppf "(size : %d)" n
    | _ :: rest-> attribute ppf (kind, rest)

  (* 表示 *)
  (* expression -> unit *)
  and expression ppf ({pexp_desc = d; pexp_attributes = attrs} as exp) =
    match d with
    | Pexp_let (flg, vs, e) -> pexp_let ppf (flg, vs, Some (e))
    | Pexp_fun (_, _, p, e) -> pexp_fun ppf (p, e)
    | Pexp_apply (e, les) -> pexp_apply ppf (e, les)
    | Pexp_match (e, cs) -> pexp_match ppf (e, cs)
    | Pexp_try (e, cs) -> pexp_try ppf (e, cs)
    | Pexp_tuple es -> pexp_tuple ppf es
    | Pexp_construct (lid, Some (e)) -> pexp_construct ppf (lid, e)
    | Pexp_record (les, _) -> pexp_record ppf les
    | Pexp_array (es) -> pexp_array ppf es
    | Pexp_ifthenelse (e1, e2, eop) -> pexp_ifthenelse ppf (e1, e2, eop)
    | Pexp_sequence (e1, e2) -> pexp_sequence ppf (e1, e2)
    | _ -> if exp = hole_of_exp exp then attribute ppf ("exp", attrs)
           else Pprintast.expression ppf (Exp.mk d)

  and value_binding ppf {pvb_pat = pn; pvb_expr = en} = match en.pexp_desc with
    | Pexp_fun (_, _, p, e) ->
       Format.fprintf ppf "%a %a"
                      pattern pn
                      value_binding (Vb.mk p e)
    | _ ->
       Format.fprintf ppf "%a = %a"
                      pattern pn
                      expression en


  and cases ppf cs =
    let case ppf {pc_lhs = pn; pc_guard = gn; pc_rhs = en} = match gn with
      | None ->
         Format.fprintf ppf "| %a -> %a"
                        pattern pn
                        expression en
      | Some (e) ->
         Format.fprintf ppf "| %a when %a -> %a"
                        pattern pn
                        expression e
                        expression en in
    List.iter (fun c -> Format.fprintf ppf "%a" case c) cs

  and field_and_exp ppf (l, e) =
    Format.fprintf ppf "%s = %a; "
                   (Longident.last l.txt)
                   expression e

  and es_tl ppf (s, tl) =
    List.iter (
        fun en ->
        Format.fprintf ppf "%s %a" s
                       expression en) tl

  and pexp_let ppf (flg, vs, eop) = match vs with
      [] -> assert false
    | first :: rest ->
       let vb_hd ppf hd =
         Format.fprintf ppf (if flg = Recursive
                             then "let rec %a"
                             else "let %a") value_binding hd in
       let vb_tl ppf tl =
         List.iter (
             fun vn ->
             Format.fprintf ppf " and %a" value_binding vn) tl in
       match eop with
       | None ->
          Format.fprintf ppf "%a %a"
                         vb_hd first
                         vb_tl rest
       | Some (e) ->
          Format.fprintf ppf "%a %a in %a"
                         vb_hd first
                         vb_tl rest
                         expression e

  and pexp_fun ppf (p, e) =
    Format.fprintf ppf "(fun %a -> %a)"
                   pattern p
                   expression e

  and pexp_apply ppf (e, les) =
    let args ppf les =
      List.iter (fun (_, e) -> Format.fprintf ppf " %a" expression e) les in
    Format.fprintf ppf "(%a%a)"
                   expression e
                   args les

  and pexp_match ppf (e, cs) =
    Format.fprintf ppf "match %a with %a"
                   expression e
                   cases cs

  and pexp_try ppf (e, cs) =
    Format.fprintf ppf "try %a with %a"
                   expression e
                   cases cs

  and pexp_tuple ppf es = match es with
      [] -> assert false
    | first :: rest ->
       Format.fprintf ppf "(%a%a)"
                      expression first
                      es_tl (",", rest)

  and pexp_construct ppf (lid, e) = (* 要素ありのみ *)
    Format.fprintf ppf "(%s %a)"
                   (Longident.last lid.txt)
                   expression e

  and pexp_record ppf les =
    Format.fprintf ppf "{%a}"
                   (fun ppf les ->
                     List.iter (field_and_exp ppf) les) les

  and pexp_array ppf es = match es with
      [] -> Format.fprintf ppf "[||]"
    | first :: rest ->
       Format.fprintf ppf "[|%a%a|]"
                      expression first
                      es_tl (";", rest)

  and pexp_ifthenelse ppf (e1, e2, eop) = match eop with
    | None ->
       Format.fprintf ppf "@if %a then %a"
                      expression e1
                      expression e2
    | Some (e3) ->
       Format.fprintf ppf "if %a then %a else %a"
                      expression e1
                      expression e2
                      expression e3

  and pexp_sequence ppf (e1, e2) =
    Format.fprintf ppf "(%a; %a)"
                   expression e1
                   expression e2
    

  and pattern ppf ({ppat_desc = d; ppat_attributes = attrs} as pat) =
    match d with
    | Ppat_tuple ps -> ppat_tuple ppf ps
    | Ppat_construct (lid, Some (p)) -> ppat_construct ppf (lid, p)
    | Ppat_record (lps, _) -> ppat_record ppf lps
    | _ -> if pat = hole_of_pat pat then attribute ppf ("pat", attrs)
           else Pprintast.pattern ppf pat

  and ppat_tuple ppf ps = match ps with
      [] -> assert false
    | first :: rest ->
       Format.fprintf
         ppf "(%a%a)"
         pattern first
         (fun ppf ps ->
           List.iter (Format.fprintf ppf ", %a" pattern) ps) rest

  and ppat_construct ppf (lid, p) = (* 要素ありのみ *)
    Format.fprintf ppf "(%s %a)"
                   (Longident.last lid.txt)
                   pattern p

  and ppat_record ppf lps =
    Format.fprintf ppf "{%a}"
                   (fun ppf lps ->
                     List.iter (field_and_pat ppf) lps) lps

  and field_and_pat ppf (l, p) =
    Format.fprintf ppf "%s = %a; "
                   (Longident.last l.txt) pattern p

  let rec structure ppf str = match str with
    | [] -> ()
    | ({pstr_desc = d} as first) :: rest ->
       (* first の表示 *)
       if first <> hole_str then
         match d with
         | Pstr_eval (e, _) ->
            Format.fprintf ppf "@[%a@]@." expression e
         | Pstr_value (flg, vs) ->
            Format.fprintf ppf "@[%a@]@." pexp_let (flg, vs, None)
         | _ ->
            Format.fprintf ppf "@[%a@]@." Pprintast.structure [first]
       else Format.fprintf ppf "@[(The mark '□' is a hole expression.)@]@.";
       (* rest について再帰 *)
       Format.fprintf ppf "@[%a@]@." structure rest

  (* デバッグ用 expression の print *)
  let print_deb_exp ppf exp =
    Format.fprintf ppf "%a %a"
                   expression exp
                   attribute ("size", exp.pexp_attributes)
  let print_deb_strs ppf strs = Format.fprintf ppf "%a"structure strs


end

(*
(* 位置情報付き dummy_false *)
let dummy_false loc = {
  pexp_desc       = Pexp_construct (mknoloc (Longident.Lident "false"), None);
  pexp_loc        = loc;
  pexp_attributes = [];
}


(* スケルトン *)
let skeleton = {
  pexp_desc       = Pexp_assert (dummy_false Location.none);
  pexp_loc        = Location.none;
  pexp_attributes = [];
}
let wildcard = {
    ppat_desc = Ppat_any;
    ppat_loc = Location.none;
    ppat_attributes = [];
  }

(* □を示すattribute：exp, pat共通 *)
(* pat にワイルドカードを渡すと exp の□ *)
(* exp にスケルトンを渡すと pat の□ *)
let hole exp pat =
  let str_loc =
    if pat = wildcard then
      {txt = "exp"; loc = exp.pexp_loc}
    else if exp = skeleton then
      {txt = "pat"; loc = pat.ppat_loc}
    else assert false in
  let p_payload = PPat (pat, if exp = skeleton then None else Some exp) in
  (str_loc, p_payload)

(* 省略前の式情報付き dummy_assertfalse *)
let dummy_assertfalse exp =
  if exp.pexp_desc = Pexp_assert (dummy_false exp.pexp_loc)
  then exp
  else {
      pexp_desc       = Pexp_assert (dummy_false exp.pexp_loc);
      pexp_loc        = exp.pexp_loc;
      pexp_attributes = hole exp wildcard :: [];
    }

(* 省略前のパターン情報付き any *)
let dummy_any pat =
  if pat.ppat_desc = Ppat_any
  then pat
  else {ppat_desc = Ppat_any;
        ppat_loc = pat.ppat_loc;
        ppat_attributes = hole skeleton pat :: [];
       }

let dummy_int0 = Exp.mk (Pexp_constant (Pconst_integer ("0", None)))

let dummy_fun = Exp.mk (Pexp_fun (Nolabel, None, wildcard, skeleton))
 *)

(* 抽象：変数 *)
let skeleton = Hole.dummy_assertfalse ()
let wildcard = Hole.dummy_any ()
let dummy_int0 = Hole.dummy_int0 ()
let dummy_fun = Hole.dummy_fun ()
(* 抽象化：関数 *)
let dummy_assertfalse exp = Hole.expression exp
let dummy_any pat = Hole.pattern pat

(* デバッグ用：変数 *)
(* 表示の切り替え *)
let print_node_count = Meta.print_node_count
let print_asked_expr = Meta.print_asked_expr
let print_slice = Meta.print_slice
let print_ocaml_error = Meta.print_ocaml_error
(* スライスの切り替え *)
let on_slice = Meta.on_exp_slice
let on_pat_slice = Meta.on_pat_slice
(* デバッグ用：関数 *)
let print_deb_exp ppf exp = Meta.print_deb_exp ppf exp
let print_deb_strs ppf strs = Meta.print_deb_strs ppf strs

(*
let print_node_count =
  false (* ノード数をカウントするときには true にする *)
        (* true にすると型デバッグはできなくなる *)
let print_asked_expr =
  false (* カウントされた質問を表示するときには true にする *)

(* スライス表示用変数 (debug_slice.ml) *)

let print_slice =
  not print_node_count && (* ノード数カウント中はスライスを表示しない *)
  false (* スライス結果を表示するときに true にする *)

(* OCaml のエラーメッセージ Errors.report_error 制御用変数
   (toplevel/toploop.ml, driver/compile.ml) *)

let print_ocaml_error =
  not print_node_count && (* ノード数カウント中は表示しない *)
  true  (* OCaml のエラーメッセージを消すときに false にする *)

(* スライスをするかどうかを制御する変数
   (debug_slice.ml, debug_main.ml) *)

let on_slice =
  print_node_count || (* ノード数カウント中はスライスを行う *)
  true (* スライスをしないときには false を代入する *)

let on_pat_slice =
  ref true (* パターンのスライスをしないときには false を代入する *)
 *)

(* ---------------------------------------------------------- *)
(* デバッガ、スライサ共通の定義 *)

let rec get_type_name typ = match typ.desc with
  | Tconstr (path, _, _) ->
     (* 定義名とモジュール名のリストを返す *)
     let lst =
       (Longident.flatten (Longident.parse (Path.name path))) in
     List.fold_left (
         fun (type_name, mod_names) s ->
         (s, if type_name = "" then mod_names
             else type_name :: mod_names)
       ) ("", []) lst
  | Tsubst (t) -> get_type_name t
  | Tlink (t) -> get_type_name t
  | _ -> assert false

let rec get_type_decl (type_name, mod_names) prefix = match prefix with
    [] -> failwith "this type was not find."
  | ({pstr_desc = d}, _) :: rest ->
     match d with
     | Pstr_module ({pmb_name = {txt = name};
                     pmb_expr = {pmod_desc =
                                   Pmod_structure (mod_str)}}) ->
        (* モジュールの定義 *)
        (* name が mod_names にある場合は mod_str も再帰に含める *)
        get_type_decl
          (type_name, mod_names)
          (if List.exists (
                  fun mod_name -> mod_name = name) mod_names
           then List.fold_left (
                    fun rest' s -> (s, Env.empty) :: rest'
                  ) rest mod_str else rest)
     | Pstr_type (_, tds) ->
        (* 型の定義 *)
        (* 名前が一致した場合に type_declaration を返す *)
        begin
          try
            let td =
              List.find (fun {ptype_name = {txt = name}} ->
                          name = type_name) tds in
            if print_slice then
              Format.fprintf ppf "@[  find type_declaration. @]@.";
            td
          with _ -> get_type_decl (type_name, mod_names) rest
        end
     | _ -> get_type_decl (type_name, mod_names) rest
    
(* decode_labels : type_expr -> prefix -> label_declaration list *)
let decode_labels typ prefix =
  match get_type_decl (get_type_name typ) prefix with
  | {ptype_kind = Ptype_record (lds)} -> lds
  | _ -> failwith "This type is not record."

(* 矢印の分離 *)
(* split_arrow : type_expr -> (type_expr * type_expr) option *)
let rec split_arrow typ = match typ.desc with
    Tarrow (_, t1, t2, _) -> Some (t1, t2)
  | Tlink (typ') -> split_arrow typ'
  | _ -> None

(* タプルの分離 *)
(* decode_tuple : type_expr -> type_expr option *)
let rec decode_tuple typ = match typ.desc with
    Ttuple (typs) -> Some (typs)
  | Tlink (typ') -> decode_tuple typ'
  | _ -> None

(* ---------------------------------------------------------- *)
(* 構文の生成 *)

(* 元の構文の desc を置き換える *)
let desc_to_exp = Desc.expression
let desc_to_pat = Desc.pattern

(*
(* desc_to_exp : expression_desc -> expression -> expression *)
let desc_to_exp desc {pexp_loc = loc; pexp_attributes = attrs} =
  Exp.mk ~loc ~attrs desc
(*
  {pexp_desc = desc; pexp_loc = exp.pexp_loc; pexp_attributes = exp.pexp_attributes} *)
(* desc_to_pat : pattern_desc -> pattern -> pattern *)
let desc_to_pat desc {ppat_loc = loc; ppat_attributes = attrs} =
  Pat.mk ~loc ~attrs desc
(*
  {ppat_desc = desc; ppat_loc = pat.ppat_loc; ppat_attributes = pat.ppat_attributes} *)
 *)

(* ---------------------------------------------------------- *)


(* pattern_variables : pattern -> string list *)
(* collect all the pattern variables in a pattern *)
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

let rec plug_expr expr cxt = match cxt with
  | Empty -> expr
  | Lambda (pat, c) ->
     (* パターン変数を全て集め *)
     let vars = pattern_variables pat in
     (* 変数名から変数の expression を作る *)
     let varexp x = Exp.ident (mknoloc (Longident.Lident x)) in
(*
     let varexp x = Exp.mk (Pexp_ident (mknoloc (Longident.Lident x))) in *)
     (* expr と組にして body に入れる。これでパターン変数の型を知る *)
     (* ダミーの 0 を入れるのは、tuple 長が 2 以上でないとエラーになるため *)
     let body = Exp.tuple (expr :: dummy_int0 :: List.map varexp vars) in
     let exp = Exp.fun_ Nolabel None pat body in
(*
     let body = Exp.mk (Pexp_tuple
                          (expr :: dummy_int0 :: List.map varexp vars)) in
     let exp = Exp.mk (Pexp_fun (Nolabel, None, pat, body)) in *)
     plug_expr exp c
  | Let (flg, bindings, c) ->
     let exp = Exp.let_ flg bindings expr in
(*
     let exp = Exp.mk (Pexp_let (flag, bindings, expr)) in

{ pexp_desc        = Pexp_let (flag, bindings, expr);
                  pexp_loc         = Location.none;
                  pexp_attributes  = [] }*)
     plug_expr exp c

(* plug_str : (expression * expr_context) -> structure *)
(*
let plug_str (expr, cxt) = [Str.mk (Pstr_eval (plug_expr expr cxt, []))]
 *)
let plug_str (expr, cxt) = [Str.eval (plug_expr expr cxt)]
(*
  [{ pstr_desc = Pstr_eval (plug_expr expr cxt, []);
     pstr_loc  = Location.none }]
 *)

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

(* collect : expression context_t -> type_expr -> yes_no_list * type_expr *)
let rec collect ((expr, cxt), env, prefix) t = match cxt with
    Empty -> ([], t)
  | Let (_, _, cxt') -> collect ((expr, cxt'), env, prefix) t
  | Lambda (pat, cxt') ->
      (* There and back again [Danvy&Goldberg ICFP'02] *)
      let (vartyps, t') = collect ((expr, cxt'), env, prefix) t in
      let vars = pattern_variables pat in
      match split_arrow t' with
          Some ((*t1*)_, t2) ->
            collect_one ((vartyps, cxt'), env, prefix) vars t2
        | None -> (* Can't happen *)
            failwith "TypeDebugger: Error in collect"

(* judge : expression context_t -> yes_no_list * type_expr *)
let judge ((expr, cxt), env, prefix) =
  let structure = plug_str (expr, cxt) in
  let (structure', _, _) = Typemod.type_structure env structure Location.none in
  match structure'.str_items with
    {str_desc = Tstr_eval ({ exp_type = typ }, _)} :: [] ->
      collect ((expr, cxt), env, prefix) typ
  | _ -> failwith "TypeDebugger: Error in judge"
