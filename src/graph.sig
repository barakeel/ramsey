signature graph =
sig

  type vertex = int
  type edge = int * int
  type color = int
  type mat = color Array2.array
  type coloring = (edge * color) list
  
  (* colors *)
  val blue : int
  val red : int
  
  (* array2 shortcuts *)
  val mat_size : mat -> int
  val mat_sub : mat * int * int -> int
  val mat_update_sym : mat * int * int * int -> unit
  val mat_tabulate : int * (int * int -> int) -> mat
  val mat_traverse : (int * int * int -> unit) -> mat -> unit
  val mat_copy : mat -> mat
  
  (* comparison functions *)
  val edge_compare : (int * int) * (int * int) -> order
  val edgec_compare : ((int * int) * int) * ((int * int) * int) -> order
  val mat_compare : mat * mat -> order
  val mat_eq : mat -> mat -> bool
  val mat_compare_fixedsize : int -> mat * mat -> order
  val mat_set : mat list -> mat list
  
  (* I/O *)
  val zip_mat : mat -> IntInf.int
  val unzip_mat : IntInf.int -> mat
  val szip_mat : mat -> string
  val sunzip_mat : string -> mat
  val zip_full : mat -> IntInf.int
  val unzip_full : int -> IntInf.int -> mat
  val unzip_full_edgecl : int -> IntInf.int -> ((int * int) * int) list
  val name_mat : mat -> string
  
  (* debug *)
  val string_of_edge : edge -> string
  val edge_of_string : string -> edge
  val string_of_edgel : edge list -> string
  val edgel_of_string : string -> edge list
  val string_of_edgec : (edge * color) -> string
  val edgec_of_string : string -> (edge * color)
  val string_of_edgecl : coloring -> string
  val edgecl_of_string : string -> coloring
  val string_of_graph : mat -> string
  val string_of_bluegraph : mat -> string
  val string_of_mat : mat -> string
  val print_mat : mat -> unit
  
  (* matrices *)
  val mat_empty : int -> mat
  val random_mat : int -> mat
  val random_full_mat : int -> mat
  val matK : int -> mat
  val diag_mat : mat -> mat -> mat
  val extend_mat : mat -> int -> mat
  
  (* mat_permute: can also be used to reduce the size of the graph *)
  val mat_permute : mat * int -> (int -> int) -> mat
  val mk_permf : int list -> (int -> int)
  val invert_perm : int list -> int list
  val symmetrify : mat -> mat
  val permutations : 'a list -> 'a list list
  val random_subgraph : int -> mat -> mat
  val mat_merge : mat -> mat -> mat option
  val mat_inject : int -> mat -> int list -> mat
   
  (* neighbors *)
  val neighbor_of : int -> mat -> int -> int list
  val commonneighbor_of : int -> mat -> int * int -> int list
  val inneighbor_of : int -> mat -> int -> int list
  val neighborm_of : int -> mat -> int -> mat
 
  (* properties *)
  val number_of_edges : mat -> int
  val number_of_holes : mat -> int
  val all_holes : mat -> edge list
  val number_of_blueedges : mat -> int
  val all_cedges : mat -> edge list
  val all_edges : int -> edge list
  val is_ramsey : (int * int) -> mat -> bool
  val all_cliques : int -> int -> mat -> int list list
  val all_5cliques : int -> mat -> (int * int * int * int * int) list
  val exist_clique : int -> (int * int -> bool) -> int list -> bool
  val exist_clique_mat : mat -> int * int -> bool
  val exist_clique_edge : mat -> int * int -> edge -> bool
  val can_extend_edge : int * int -> mat -> edge -> bool
  val all_clique_mat : mat -> int * int -> (int list) list
  
  (* converting from matrix representation to list of edges *)
  val mat_to_edgecl : mat -> coloring
  val edgecl_to_mat : int -> coloring -> mat
  
  (* applying colorings *)
  val all_coloring : edge list -> coloring list
  val apply_coloring : mat -> coloring -> mat
  val swap_colors : mat -> mat
  
   
end
