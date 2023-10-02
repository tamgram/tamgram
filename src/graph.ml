let get_id =
  let id = ref 0 in
  (fun () ->
     let r = !id in
     id := r + 1;
     r
  )

type 'a t = {
  succ : Int_set.t Int_map.t;
  pred : Int_set.t Int_map.t;
  vertices : 'a Int_map.t;
}

let empty = {
  succ = Int_map.empty;
  pred = Int_map.empty;
  vertices = Int_map.empty
}

let is_empty (t : 'a t) =
  Int_map.is_empty t.vertices

let union (t1 : 'a t) (t2 : 'a t) =
  {
    succ = Int_map.union
        (fun _k x y -> Some (Int_set.union x y))
        t1.succ t2.succ;
    pred = Int_map.union
        (fun _k x y -> Some (Int_set.union x y))
        t1.pred t2.pred;
    vertices = Int_map.union
        (fun _k x y -> assert (x = y); Some x)
        t1.vertices t2.vertices;
  }

let vertices (t : 'a t) = t.vertices

let vertex_seq (t : 'a t) : (int * 'a) Seq.t =
  Int_map.to_seq (vertices t)

let succ (x : int) (t : 'a t) =
  Option.value ~default:Int_set.empty
    (Int_map.find_opt x t.succ)

let succ_seq x t =
  Int_set.to_seq (succ x t)

let pred (x : int) (t : 'a t) =
  Option.value ~default:Int_set.empty
    (Int_map.find_opt x t.pred)

let pred_seq x t =
  Int_set.to_seq (pred x t)

let edges (t : 'a t) =
  Int_map.fold (fun key successors acc ->
      Int_set.fold (fun x acc ->
          Int_int_set.add (key, x) acc
        ) successors acc
    ) t.succ Int_int_set.empty

let edge_seq (t : 'a t) =
  edges t
  |> Int_int_set.to_seq

let map (f : 'a -> 'b) (m : 'a t) : 'b t =
  {
    m with
    vertices = Int_map.map f m.vertices;
  }

let find_opt (id : int) (t : 'a t) =
  Int_map.find_opt id t.vertices

let find (id : int) (t : 'a t) =
  CCOption.get_exn_or "graph: Failed to find vertex"
    (find_opt id t)

let mem_edge ((x, y) : int * int) (t : 'a t) =
  match find_opt x t with
  | None -> false
  | Some _ ->
    Int_set.mem y (succ x t)

let roots (t : 'a t) =
  Int_map.to_seq t.vertices
  |> Seq.filter_map
    (fun (key, _) ->
       if Int_set.is_empty (pred key t) then
         Some key
       else
         None
    )

let leaves (t : 'a t) =
  Int_map.to_seq t.vertices
  |> Seq.filter_map
    (fun (key, _) ->
       if Int_set.is_empty (succ key t) then
         Some key
       else
         None
    )

let add_vertex_with_id (id : int) (v : 'a) (t : 'a t) : 'a t =
  { t with vertices = Int_map.add id v t.vertices }

let add_vertex (v : 'a) (t : 'a t) : 'a t * int =
  let id = get_id () in
  (add_vertex_with_id id v t, id)

let add_edge ((x, y) : int * int) (t : 'a t) =
  {
    t with
    succ = Int_map.update x (fun s ->
        let s = Option.value ~default:Int_set.empty s in
        Some Int_set.(add y s)
      ) t.succ;
    pred = Int_map.update y (fun s ->
        let s = Option.value ~default:Int_set.empty s in
        Some Int_set.(add x s)
      ) t.pred;
  }

let paths_from_id ~max_loop_count (id : int) (t : 'a t) : int list Seq.t =
  let appear_at_most_count =
    max_loop_count + 1
  in
  let rec aux (seen : int Int_map.t) id t : int list Seq.t =
    let seen_count_so_far =
      Option.value ~default:0 (Int_map.find_opt id seen)
    in
    let seen_count_now =
      seen_count_so_far + 1
    in
    if seen_count_now > appear_at_most_count then (
      Seq.return []
    ) else (
      let successors = succ_seq id t in
      match successors () with
      | Seq.Nil -> Seq.return [id]
      | Seq.Cons _ ->
        successors
        |> Seq.flat_map (fun x ->
            aux (Int_map.add id seen_count_now seen) x t
          )
        |> Seq.map (fun l ->
            id :: l
          )
    )
  in
  if max_loop_count < 0 then (
    invalid_arg "max_loop_count < 0"
  );
  aux Int_map.empty id t

let paths_from_roots ~max_loop_count (t : 'a t) : int list Seq.t =
  roots t
  |> Seq.flat_map (fun id ->
      paths_from_id ~max_loop_count id t
    )
