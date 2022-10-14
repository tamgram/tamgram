type 'a t

val get_id : unit -> int

val empty : 'a t

val union : 'a t -> 'a t -> 'a t

val vertices : 'a t -> 'a Int_map.t

val vertex_seq : 'a t -> (int * 'a) Seq.t

val edges : 'a t -> Int_int_set.t

val edge_seq : 'a t -> (int * int) Seq.t

val map : ('a -> 'b) -> 'a t -> 'b t

val find : int -> 'a t -> 'a

val find_opt : int -> 'a t -> 'a option

val mem_edge : int * int -> 'a t -> bool

val pred : int -> 'a t -> Int_set.t

val pred_seq : int -> 'a t -> int Seq.t

val succ : int -> 'a t -> Int_set.t

val succ_seq : int -> 'a t -> int Seq.t

val roots : 'a t -> int Seq.t

val leaves : 'a t -> int Seq.t

val add_vertex_with_id : int -> 'a -> 'a t -> 'a t

val add_vertex : 'a -> 'a t -> 'a t * int

val add_edge : (int * int) -> 'a t -> 'a t

val paths_from_id : max_loop_count:int -> int -> 'a t -> int list Seq.t

val paths_from_roots : max_loop_count:int -> 'a t -> int list Seq.t
