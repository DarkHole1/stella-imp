open AbsStella

type t = Context of (string * typeT) list * string list

let empty = Context ([], [])
let from_var (s : string) (ty : typeT) : t = Context ((s, ty) :: [], [])
let from_type (s : string) : t = Context ([], s :: [])

let put (Context (vars, types) : t) (s : string) (ty : typeT) : t =
  Context ((s, ty) :: vars, types)

let get (Context (vars, _) : t) (s : string) : typeT option =
  List.assoc_opt s vars

let put_type (Context (vars, types) : t) (s : string) : t =
  Context (vars, s :: types)

let has_type (Context (_, types) : t) (s : string) : bool = List.mem s types

let merge (Context (vars, types) : t) (Context (vars', types') : t) : t =
  Context (List.concat [ vars; vars' ], List.concat [ types; types' ])

let concat (ctxs : t list) : t = List.fold_left merge empty ctxs

let map (f : string * typeT -> string * typeT) (Context (vars, types)) =
  Context (List.map f vars, types)
