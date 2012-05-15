module Vertex =  struct
    type t = int
    let compare = compare
    let hash x = x
    let equal a b = a = b
    let pretty fmt = Format.fprintf fmt "%d"
end
module EdgeLabel = struct
    type t = Single | Mult
    let compare a b = match a, b with
      | Single, Mult -> -1
      | Mult, Single -> 1
      | _, _ -> 0
    let default = Single
    let join a b = match a, b with
      | Single, Single -> Single
      | _, _ -> Mult
    let pretty fmt = function
      | Single -> Format.fprintf fmt "s"
      | Mult -> Format.fprintf fmt "m"
end

module MyGraph = Dualgraph.Make (Vertex) (EdgeLabel)

include MyGraph
include Graph.Builder.P (MyGraph)
include Graph.Graphviz.Dot (struct
  include MyGraph
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_name v = string_of_int v
  let vertex_attributes _ = []
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes (_, l, _)  = [`Label (match l with
    | EdgeLabel.Single -> "s"
    | EdgeLabel.Mult -> "m")]
end)

let out_graph file g =
  let fh = open_out file in
  output_graph fh g;
  close_out_noerr fh

let g1 =
  let g = empty () in
  let g = List.fold_left (fun accu x -> add_vertex accu x) g [1;2;3;4] in
  let g = add_edge g 1 4 in
  let g = add_edge g 1 2 in
  let g = add_edge g 3 2 in
  let g = add_edge g 4 2 in
  g
