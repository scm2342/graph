open Graph

(* special graph that basecally represents a mixture between adjecency matrices
 * and adjecency lists - this should speed up predecessor operations...
 * current limitation: only one edge allowed between two nodes
 *)
(* invariants that must be preserved:
  * The set of vertexes in the graph is equal to the set of keys of fwgraph and
  * bwgraph
  * Whenever there exists an edge from a -> b in fwgraph, there exists an edge
  * b -> a in the bwgraph and vice versa
  * The number of edges within fwgraph and bwgraph is edges
  *)
module Make
  (V : sig
    include Sig.COMPARABLE
    val pretty : Format.formatter -> t -> unit
  end)
  (L : sig
    include Sig.ORDERED_TYPE_DFT
    val pretty : Format.formatter -> t -> unit
  end)
: Sig.P with type V.t = V.t and type V.label = V.t
        and type E.t = V.t * L.t * V.t and type E.label = L.t = struct
  module V = struct
    include V
    type label = V.t
    let create x = x
    let label x = x
  end
  module E = struct
    type vertex = V.t
    type label = L.t
    type t = vertex * label * vertex
    let src (s, _, _) = s
    let dst (_, _, d) = d
    let label (_, l, _) = l
    let create s l d = s, l, d
    let compare (s1, l1, d1) (s2, l2, d2) =
      let compare_bind prev_compare next_compare =
        if prev_compare != 0 then prev_compare else
          next_compare ()
      in
      compare_bind (compare s1 s2) (fun () ->
      compare_bind (compare l1 l2) (fun () ->
                   (compare d1 d2)))
  end
  module VSet = Set.Make (V)
  module VMap = struct
    include Map.Make (V)
    let merge_with f = merge (fun k a b -> match a, b with
      | Some a, Some b -> Some (f a b)
      | Some a, None -> Some a
      | None, Some b -> Some b
      | None, None -> None)
  end

  type graph = E.label VMap.t VMap.t
  type ordering = V.t list

  type t = { fwgraph : graph
           ; bwgraph : graph
           ; edges : int }

  type vertex = V.t
  type edge = E.t

  module Debug = struct
    include Graphviz.Dot (struct
      type t = graph
      module V = V
      module E = E
      let iter_vertex f = VMap.iter (fun k _ -> f k)
      let iter_edges_e f = VMap.iter
        (fun s v ->
          VMap.iter (fun d l -> f (s, l, d)) v
        )
      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let vertex_name v =
        V.pretty Format.str_formatter v; Format.flush_str_formatter ()
      let vertex_attributes _ = []
      let get_subgraph _ = None
      let default_edge_attributes _ = []
      let edge_attributes (_, l, _) =
        let str =
          L.pretty Format.str_formatter l; Format.flush_str_formatter ()
        in
        [`Label str]
    end)
    let out fn g =
      let fh = open_out fn in
      output_graph fh g;
      close_out_noerr fh
  end

  let is_directed = true

  let nb_vertex { fwgraph = g } = VMap.cardinal g
  let nb_edges { edges = n } = n
  let is_empty = function ({ edges = 0 } as g) -> nb_vertex g = 0 | _ -> false
  let degree g v =
    try
      VMap.cardinal (VMap.find v g)
    with Not_found -> raise (Invalid_argument "could not find vertex in graph")
  let out_degree { fwgraph = g } = degree g
  let in_degree { bwgraph = g } = degree g

  let mem_vertex { fwgraph = g } v = VMap.mem v g
  let mem_edge { fwgraph = g } s d =
    try
      VMap.mem d (VMap.find s g)
    with Not_found -> false
  let mem_edge_e { fwgraph = g } (s, l, d) =
    try
      L.compare (VMap.find d (VMap.find s g)) l = 0
    with Not_found -> false
  let find_edge { fwgraph = g } s d =
    s, VMap.find d (VMap.find s g), d
  let find_all_edges g s d = [find_edge g s d]

  let fold_gen_e f g v accu =
    try
      VMap.fold (fun k l -> f (v, l, k)) (VMap.find v g) accu
    with Not_found -> accu
  let fold_succ_e f { fwgraph = g } = fold_gen_e f g
  let iter_succ_e f g v = fold_succ_e (fun e _ -> f e) g v ()
  let fold_pred_e f { bwgraph = g } = fold_gen_e f g
  let iter_pred_e f g v = fold_pred_e (fun e _ -> f e) g v ()

  let fold_gen f = fold_gen_e (fun (_, _, k) -> f k)
  let fold_succ f { fwgraph = g } = fold_gen f g
  let iter_succ f g v = fold_succ (fun s _ -> f s) g v ()
  let fold_pred f { bwgraph = g } = fold_gen f g
  let iter_pred f g v = fold_pred (fun p _ -> f p) g v ()

  let succ g v = fold_succ (fun s acc -> s :: acc) g v []
  let pred g v = fold_pred (fun p acc -> p :: acc) g v []
  let succ_e g v = fold_succ_e (fun e acc -> e :: acc) g v []
  let pred_e g v = fold_pred_e (fun e acc -> e :: acc) g v []

  let fold_vertex f { fwgraph = g } = VMap.fold (fun v _ -> f v) g
  let iter_vertex f g = fold_vertex (fun v _ -> f v) g ()
  let fold_edges_e f { fwgraph = g } = VMap.fold
    (fun s lmap accu -> VMap.fold (fun d l -> f (s, l, d)) lmap accu) g
  let iter_edges_e f g = fold_edges_e (fun e _ -> f e) g ()
  let fold_edges f = fold_edges_e (fun (s, _, d) -> f s d)
  let iter_edges f g = fold_edges (fun s d _ -> f s d) g ()
  (* this is f'in expensive...
   * but, the official ocaml graph one applies f to the keys and to all targets
   * that way, if f is not pure, there is imho the potential for total fuckup
   * also, it is expected that f is surjective since otherwise map again has
   * an effect on edges...
   * This is probably not the nicest solution, however my alternative would have
   * been assert false and that may have fucked up other stuff...
   * the end is nigh - cthulhu is emerging!
   *)
  let map_vertex f ({ fwgraph = fg; bwgraph = bg } as g) =
    let cache = Hashtbl.create (nb_vertex g) in
    let surjective_checker = ref VSet.empty in
    let f_memoized v =
      try Hashtbl.find cache v with Not_found ->
        let res = f v in
        if (VSet.mem res !surjective_checker) then raise (Invalid_argument
          "Detected non surjective f as argument to map_vertex");
        surjective_checker := VSet.add res !surjective_checker;
        Hashtbl.add cache v res;
        res
    in
    let map_one g = VMap.fold (fun k v accu -> VMap.add (f_memoized k)
      (VMap.fold (fun k v accu -> VMap.add (f_memoized k) v accu) v VMap.empty)
      accu
      )
      g
      VMap.empty
    in
    { g with fwgraph = map_one fg; bwgraph = map_one bg }

  let empty = { fwgraph = VMap.empty; bwgraph = VMap.empty; edges = 0 }
  let add_vertex ({ fwgraph = fg; bwgraph = bg } as g) v =
    let add_one g =
      VMap.merge_with (fun a _ -> a) g (VMap.singleton v (VMap.empty))
    in
    { g with fwgraph = add_one fg; bwgraph = add_one bg }
  let remove_vertex ({ fwgraph = fg; bwgraph = bg; edges = edges } as g) v =
    let fwval = try Some (VMap.find v fg) with Not_found -> None in
    let bwval = try Some (VMap.find v bg) with Not_found -> None in
    match fwval, bwval with
      | Some _, None -> assert false (* invariant *)
      | None, Some _ -> assert false (* invariant *)
      | None, None   -> g
      | Some fwval, Some bwval ->
        let update_one g to_del_map =
          VMap.fold
           (fun s _ (acc, del_e) ->
             if V.equal s v then (acc, del_e) else begin
               let (res, del_e') = (VMap.fold
                 (fun d l (acc', del_e') ->
                   if V.equal d v then (acc', del_e' + 1)
                   else (VMap.add d l acc', del_e')
                 )
                 (VMap.find s acc)
                 (VMap.empty, del_e)
               )
               in
               (VMap.add s res acc, del_e + del_e')
             end
           )
           to_del_map
           (VMap.remove v g, 0)
        in
        let (new_fw, f_del_e) = update_one fg bwval in
        let f_del_e = f_del_e + VMap.cardinal fwval in
        let (new_bw, b_del_e) = update_one bg fwval in
        let b_del_e = b_del_e + VMap.cardinal bwval in
        assert (f_del_e = b_del_e);
        { fwgraph = new_fw
        ; bwgraph = new_bw
        ; edges = edges - f_del_e }
  let add_edge_e ({ fwgraph = fg; bwgraph = bg; edges = edges } as g) e =
    let add_edge_one g (s, l, d) =
      VMap.merge_with
        (fun a b -> VMap.merge_with (fun _ _ -> assert false) a b)
        (VMap.singleton s (VMap.singleton d l)) g
    in
    if mem_edge g (E.src e) (E.dst e) then g else
    add_vertex
      { fwgraph = add_edge_one fg e
      ; bwgraph = add_edge_one bg (E.create (E.dst e) (E.label e) (E.src e))
      ; edges = edges + 1 }
      (E.src e)
  let add_edge g s d = add_edge_e g (E.create s L.default d)
  let remove_edge_gen { fwgraph = fg; bwgraph = bg; edges = edges } s d f =
    let remove_edge_one g s d =
      try
        let edges = VMap.find s g in
        let label = VMap.find d edges in
        if f label
        then VMap.add s (VMap.remove d edges) g, true
        else g, false
      with Not_found -> raise (Invalid_argument "Could not find vertices")
    in
    let (new_fg, removed_f) = remove_edge_one fg s d in
    let (new_bg, removed_b) = remove_edge_one bg d s in
    assert (removed_f = removed_b);
    { fwgraph = new_fg
    ; bwgraph = new_bg
    ; edges = if removed_f then edges - 1 else edges }
  let remove_edge_e g (s, l, d) = remove_edge_gen g s d
    (fun x -> L.compare l x = 0)
  let remove_edge g s d = remove_edge_gen g s d (fun _ -> true)
end
