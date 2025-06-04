open AbsStella
open Utils
open Errors

type context = Context.t

let make_eq (restrictions : (typeT * typeT) list ref) =
  let rec eq (ty1 : typeT) (ty2 : typeT) : bool =
    match (ty1, ty2) with
    | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
        List.compare_lengths tyArgs1 tyArgs2 = 0
        && List.for_all2 eq tyArgs1 tyArgs2
        && eq tyRet1 tyRet2
    | TypeSum (ty11, ty12), TypeSum (ty21, ty22) -> eq ty11 ty21 && eq ty12 ty22
    | TypeTuple tys1, TypeTuple tys2 ->
        List.compare_lengths tys1 tys2 = 0 && List.for_all2 eq tys1 tys2
    | TypeRecord fields1, TypeRecord fields2 ->
        List.compare_lengths fields1 fields2 = 0
        && List.for_all2
             (fun (ARecordFieldType (StellaIdent name1, ty1))
                  (ARecordFieldType (StellaIdent name2, ty2)) ->
               name1 = name2 && eq ty1 ty2)
             fields1 fields2
    | TypeVariant fields1, TypeVariant fields2 ->
        List.compare_lengths fields1 fields2 = 0
        && List.for_all2
             (fun (AVariantFieldType (StellaIdent name1, typing1))
                  (AVariantFieldType (StellaIdent name2, typing2)) ->
               name1 = name2
               &&
               match (typing1, typing2) with
               | SomeTyping ty1, SomeTyping ty2 -> eq ty1 ty2
               | NoTyping, NoTyping -> true
               | _ -> false)
             fields1 fields2
    | TypeList ty1, TypeList ty2 -> eq ty1 ty2
    | TypeBool, TypeBool -> true
    | TypeNat, TypeNat -> true
    | TypeUnit, TypeUnit -> true
    | TypeRef ty1, TypeRef ty2 -> eq ty1 ty2
    | TypeBottom, TypeBottom -> true
    | TypeVar (StellaIdent name1), TypeVar (StellaIdent name2) ->
        if name1 = name2 then true
        else if String.starts_with ~prefix:"?" name1 then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | TypeVar (StellaIdent name), _ ->
        if String.starts_with ~prefix:"?" name then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | _, TypeVar (StellaIdent name) ->
        if String.starts_with ~prefix:"?" name then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | _ -> false
  in
  eq

(* TODO: Check creation *)
let neq (ty1 : typeT) (ty2 : typeT) : bool = make_eq (ref []) ty1 ty2 |> not

let rec subtype (ty1 : typeT) (ty2 : typeT) : bool =
  (* print_endline
    ("Checking subtype "
    ^ PrintStella.printTree PrintStella.prtTypeT ty1
    ^ " with supertype "
    ^ PrintStella.printTree PrintStella.prtTypeT ty2); *)
  match (ty1, ty2) with
  | _, TypeTop -> true
  | TypeBottom, _ -> true
  | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
      List.compare_lengths tyArgs1 tyArgs2 = 0
      && List.for_all2 subtype tyArgs1 tyArgs2
      && subtype tyRet2 tyRet1
  | TypeSum (ty11, ty12), TypeSum (ty21, ty22) ->
      subtype ty11 ty21 && subtype ty12 ty22
  | TypeRecord fields1, TypeRecord fields2 ->
      let fields' =
        List.map
          (fun (ARecordFieldType (StellaIdent name, ty)) -> (name, ty))
          fields1
      in
      List.compare_lengths fields1 fields2 >= 0
      && List.for_all
           (fun (ARecordFieldType (StellaIdent name, ty)) ->
             match List.assoc_opt name fields' with
             | Some ty' -> subtype ty' ty
             | _ -> false)
           fields2
  | TypeVariant fields1, TypeVariant fields2 ->
      let fields' =
        List.map
          (fun (AVariantFieldType (StellaIdent name, typing)) -> (name, typing))
          fields2
      in
      List.compare_lengths fields1 fields2 <= 0
      && List.for_all
           (fun (AVariantFieldType (StellaIdent name, typing')) ->
             match List.assoc_opt name fields' with
             | Some typing -> (
                 match (typing', typing) with
                 | SomeTyping ty', SomeTyping ty -> subtype ty' ty
                 | NoTyping, NoTyping -> true
                 | _ -> false)
             | None -> false)
           fields1
  | TypeList ty1, TypeList ty2 -> subtype ty1 ty2
  | TypeBool, TypeBool -> true
  | TypeNat, TypeNat -> true
  | TypeUnit, TypeUnit -> true
  | TypeRef ty1, TypeRef ty2 -> subtype ty1 ty2 && subtype ty2 ty1
  | _ -> false

let check_main (ctx : context) : unit =
  match Context.get ctx "main" with None -> missing_main () | _ -> ()

let rec synthesis_by_type (ty : typeT) : expr =
  match ty with
  (*
  | TypeAuto
  | TypeFun of typeT list * typeT
  | TypeForAll of stellaIdent list * typeT
  | TypeRec of stellaIdent * typeT
  *)
  | TypeSum (tyL, tyR) -> Inl (synthesis_by_type tyL)
  | TypeTuple types -> Tuple (List.map synthesis_by_type types)
  | TypeRecord fieldTypes ->
      let fields =
        List.map
          (fun (ARecordFieldType (ident, ty)) ->
            ABinding (ident, synthesis_by_type ty))
          fieldTypes
      in
      Record fields
  | TypeVariant (AVariantFieldType (ident, typing) :: _) ->
      let data =
        match typing with
        | SomeTyping ty -> SomeExprData (synthesis_by_type ty)
        | NoTyping -> NoExprData
      in
      Variant (ident, data)
  | TypeList _ -> List []
  | TypeBool -> ConstFalse
  | TypeNat -> ConstInt 0
  | TypeUnit -> ConstUnit
  (*
  | TypeTop
  | TypeBottom
  | TypeRef of typeT
  | TypeVar of stellaIdent
  *)
  | _ -> not_implemented "synthesis_by_type"

let rec matches (p : pattern) (term : expr) : bool =
  match (p, term) with
  (*
    | PatternCastAs of pattern * typeT
    *)
  | PatternAsc (p', _), _ -> matches p' term
  | PatternVariant (ident, NoPatternData), Variant (ident', NoExprData) ->
      ident = ident'
  | ( PatternVariant (ident, SomePatternData p'),
      Variant (ident', SomeExprData expr') ) ->
      ident = ident' && matches p' expr'
  | PatternInl p', Inl expr' -> matches p' expr'
  | PatternInr p', Inr expr' -> matches p' expr'
  | PatternTuple ps, Tuple exprs -> List.for_all2 matches ps exprs
  | PatternRecord lps, Record fields ->
      let fields' =
        List.map (fun (ABinding (ident, expr)) -> (ident, expr)) fields
      in
      List.map
        (fun (ALabelledPattern (ident, p')) -> (p', List.assoc ident fields'))
        lps
      |> List.for_all (fun (p', expr') -> matches p' expr')
  | PatternList ps, List exprs ->
      List.compare_lengths ps exprs = 0 && List.for_all2 matches ps exprs
  | PatternCons (p1, p2), List (e1 :: e2) ->
      matches p1 e1 && matches p2 (List e2)
  | PatternFalse, ConstFalse -> true
  | PatternTrue, ConstTrue -> true
  | PatternUnit, ConstUnit -> true
  | PatternInt n, ConstInt n' -> n = n'
  | PatternSucc p', ConstInt n -> n > 0 && matches p' (ConstInt (n - 1))
  | PatternVar _, _ -> true
  | _ -> false

let[@warning "-partial-match"] next_variant (Variant (ident, _))
    (TypeVariant fields) =
  let index =
    List.mapi (fun a b -> (b, a)) fields
    |> List.find_map (fun (AVariantFieldType (ident', _), idx) ->
           if ident = ident' then Some idx else None)
    |> Option.get
  in
  match List.nth_opt fields (index + 1) with
  | Some (AVariantFieldType (ident', NoTyping)) ->
      Some (Variant (ident', NoExprData))
  | Some (AVariantFieldType (ident', SomeTyping ty')) ->
      Some (Variant (ident', SomeExprData (synthesis_by_type ty')))
  | None -> None

let rec next_unmatched (p : pattern) (term : expr) (ty : typeT) : expr option =
  match (p, term, ty) with
  (*
    | PatternCastAs of pattern * typeT
    *)
  | PatternAsc (p', _), _, _ -> next_unmatched p' term ty
  | ( PatternVariant (ident, NoPatternData),
      Variant (_, NoExprData),
      TypeVariant fields ) ->
      next_variant term ty
  | ( PatternVariant (ident, SomePatternData p'),
      Variant (_, SomeExprData expr'),
      TypeVariant fields ) -> (
      let ty' =
        List.find_map
          (fun (AVariantFieldType (ident', ty)) ->
            if ident = ident' then
              match ty with SomeTyping ty' -> Some ty' | NoTyping -> None
            else None)
          fields
        |> Option.get
      in
      match next_unmatched p' expr' ty' with
      | Some expr'' -> Some (Variant (ident, SomeExprData expr''))
      | None -> next_variant term ty)
  | PatternInl p', Inl expr', TypeSum (tyL, tyR) -> (
      match next_unmatched p' expr' tyL with
      | Some expr'' -> Some (Inl expr'')
      | None -> Some (Inr (synthesis_by_type tyR)))
  | PatternInr p', Inr expr', TypeSum (tyL, tyR) -> (
      match next_unmatched p' expr' tyR with
      | Some expr'' -> Some (Inr expr'')
      | None -> None)
  | PatternTuple (p' :: ps), Tuple (expr' :: exprs), TypeTuple (ty' :: tys) -> (
      match next_unmatched (PatternTuple ps) (Tuple exprs) (TypeTuple tys) with
      | Some (Tuple exprs') -> Some (Tuple (expr' :: exprs'))
      | _ -> (
          match next_unmatched p' expr' ty' with
          | Some expr'' ->
              Some (Tuple (expr'' :: List.map synthesis_by_type tys))
          | _ -> None))
  | ( PatternRecord (ALabelledPattern (ident, lp) :: lps),
      Record fields,
      TypeRecord tys ) -> (
      let tysL =
        List.map (fun (ARecordFieldType (ident, ty)) -> (ident, ty)) tys
      in
      let fieldsL =
        List.map (fun (ABinding (ident, field)) -> (ident, field)) fields
      in
      let ty = List.assoc ident tysL in
      let expr' = List.assoc ident fieldsL in
      let tys' =
        List.filter (fun (ARecordFieldType (ident', _)) -> ident <> ident') tys
      in
      let fields' =
        List.filter (fun (ABinding (ident', _)) -> ident <> ident') fields
      in
      match
        next_unmatched (PatternRecord lps) (Record fields') (TypeRecord tys')
      with
      | Some (Record fields'') ->
          Some (Record (ABinding (ident, expr') :: fields''))
      | _ -> (
          match next_unmatched lp expr' ty with
          | Some expr'' ->
              let fields'' =
                ABinding (ident, expr'')
                :: List.map
                     (fun (ARecordFieldType (ident, ty')) ->
                       ABinding (ident, synthesis_by_type ty'))
                     tys'
              in
              Some (Record fields'')
          | None -> None))
  | PatternList (p' :: ps), List (expr' :: exprs), TypeList ty' -> (
      match next_unmatched (PatternList ps) (List exprs) ty with
      | Some (List exprs') -> Some (List (expr' :: exprs'))
      | _ -> (
          match next_unmatched p' expr' ty' with
          | Some expr'' -> Some (List [ expr'' ])
          | None -> None))
  | PatternList [], List [], TypeList ty' ->
      Some (List [ synthesis_by_type ty' ])
  | PatternCons (p1, p2), List (e1 :: e2), TypeList ty' -> (
      match next_unmatched p2 (List e2) ty with
      | Some (List exprs') -> Some (List (e1 :: exprs'))
      | _ -> (
          match next_unmatched p1 e1 ty' with
          | Some expr'' -> Some (List [ expr'' ])
          | None -> None))
  | PatternFalse, ConstFalse, TypeBool -> Some ConstTrue
  | PatternTrue, ConstTrue, TypeBool -> None
  | PatternUnit, ConstUnit, TypeUnit -> None
  | PatternInt n, ConstInt _, TypeNat -> Some (ConstInt (n + 1))
  | PatternSucc p', ConstInt n, TypeNat -> (
      match next_unmatched p' (ConstInt (n - 1)) TypeNat with
      | Some (ConstInt n') -> Some (ConstInt (n' + 1))
      | _ -> None)
  | PatternVar _, _, _ -> None
  | _ -> None

let check_exhaustivness (ps : pattern list) (ty : typeT) : expr option =
  match ty with
  (* W/O cast as if it typecheked -> there is wildcard *)
  | TypeFun _ -> None
  | TypeTop -> None
  | TypeBottom -> None
  | TypeRef _ -> None
  | _ ->
      let init = synthesis_by_type ty in
      let rec check_exhaustivness' (term : expr) : expr option =
        match List.find_opt (fun p -> matches p term) ps with
        | Some p -> (
            match next_unmatched p term ty with
            | Some term' -> check_exhaustivness' term'
            | None -> None)
        | None -> Some term
      in
      check_exhaustivness' init

let rec deconstruct_pattern_binder (p : pattern) (ty : typeT) : context =
  match (p, ty) with
  (*
  | PatternCastAs of pattern * typeT
  *)
  | PatternAsc (p', ty'), _ ->
      if neq ty' ty then unexpected_pattern_for_type p ty
      else deconstruct_pattern_binder p' ty
  | PatternVariant (StellaIdent name, patternData), TypeVariant fieldTypes -> (
      let rec find fieldTypes =
        match fieldTypes with
        | AVariantFieldType (StellaIdent name', typing) :: fieldTypes' ->
            if name = name' then typing else find fieldTypes'
        | _ -> unexpected_pattern_for_type p ty
      in
      let typing = find fieldTypes in
      match (typing, patternData) with
      | SomeTyping ty', SomePatternData p' -> deconstruct_pattern_binder p' ty'
      | NoTyping, NoPatternData -> Context.empty
      | _ -> unexpected_pattern_for_type p ty)
  | PatternVariant _, _ -> unexpected_pattern_for_type p ty
  | PatternInl p', TypeSum (tyL, _) -> deconstruct_pattern_binder p' tyL
  | PatternInl _, _ -> unexpected_pattern_for_type p ty
  | PatternInr p', TypeSum (_, tyR) -> deconstruct_pattern_binder p' tyR
  | PatternInr _, _ -> unexpected_pattern_for_type p ty
  | PatternTuple ps, TypeTuple types ->
      if List.compare_lengths ps types <> 0 then
        unexpected_pattern_for_type p ty
      else
        List.combine ps types
        |> List.map (fun (p', ty') -> deconstruct_pattern_binder p' ty')
        |> Context.concat
  | PatternTuple _, _ -> unexpected_pattern_for_type p ty
  | PatternRecord lps, TypeRecord ftys ->
      (* TODO Check fields *)
      let types =
        List.map
          (fun (ARecordFieldType (StellaIdent name, ty)) -> (name, ty))
          ftys
      in
      List.map
        (fun (ALabelledPattern (StellaIdent name, p')) ->
          List.assoc name types |> deconstruct_pattern_binder p')
        lps
      |> Context.concat
  | PatternRecord _, _ -> unexpected_pattern_for_type p ty
  | PatternList ps, TypeList ty' ->
      List.map (fun p' -> deconstruct_pattern_binder p' ty') ps
      |> Context.concat
  | PatternList _, _ -> unexpected_pattern_for_type p ty
  | PatternCons (p1, p2), TypeList ty' ->
      Context.concat
        [ deconstruct_pattern_binder p1 ty'; deconstruct_pattern_binder p2 ty ]
  | PatternCons _, _ -> unexpected_pattern_for_type p ty
  | PatternFalse, TypeBool -> Context.empty
  | PatternFalse, _ -> unexpected_pattern_for_type p ty
  | PatternTrue, TypeBool -> Context.empty
  | PatternTrue, _ -> unexpected_pattern_for_type p ty
  | PatternUnit, TypeUnit -> Context.empty
  | PatternUnit, _ -> unexpected_pattern_for_type p ty
  | PatternInt _, TypeNat -> Context.empty
  | PatternInt _, _ -> unexpected_pattern_for_type p ty
  | PatternSucc p', TypeNat -> deconstruct_pattern_binder p' TypeNat
  | PatternSucc _, _ -> unexpected_pattern_for_type p ty
  | PatternVar (StellaIdent name), _ -> Context.from_var name ty
  | _, _ -> not_implemented "deconstruct_pattern_binder"

let find_dup (xs : string list) =
  let rec find_dup' (xs : string list) (dup : string list) =
    match xs with
    | x :: xs' ->
        let dup' =
          if List.mem x xs' && not (List.mem x dup) then x :: dup else dup
        in
        find_dup' xs' dup'
    | _ -> dup
  in
  find_dup' xs []

let rec check_type (ctx : context) (ty : typeT) =
  match ty with
  | TypeFun (types, res) ->
      List.iter (check_type ctx) types;
      check_type ctx res
  | TypeSum (ty1, ty2) ->
      check_type ctx ty1;
      check_type ctx ty2
  | TypeTuple types -> List.iter (check_type ctx) types
  | TypeRecord fieldTypes ->
      let dup =
        List.map
          (fun (ARecordFieldType (StellaIdent name, _)) -> name)
          fieldTypes
        |> find_dup
      in
      if List.compare_length_with dup 0 > 0 then
        duplicate_record_type_fields dup ty
      else
        List.map (fun (ARecordFieldType (_, ty)) -> ty) fieldTypes
        |> List.iter (check_type ctx)
  | TypeVariant varTypes ->
      let dup =
        List.map
          (fun (AVariantFieldType (StellaIdent name, _)) -> name)
          varTypes
        |> find_dup
      in
      if List.compare_length_with dup 0 > 0 then
        duplicate_variant_type_fields dup ty
      else
        List.filter_map
          (fun (AVariantFieldType (_, typing)) ->
            match typing with SomeTyping ty -> Some ty | NoTyping -> None)
          varTypes
        |> List.iter (check_type ctx)
  | TypeList ty -> check_type ctx ty
  | TypeRef ty -> check_type ctx ty
  | TypeVar (StellaIdent name) ->
      if String.starts_with ~prefix:"?" name || Context.has_type ctx name then
        ()
      else undefined_type_variable ty
  | _ -> ()

let rec fresh_decls (fresh_var : unit -> string) (decls : decl list) : decl list
    =
  let fresh_var' () = StellaIdent (fresh_var ()) in
  let fresh_type =
    let rec fresh_type' (traverse : typeT -> typeT) = function
      | TypeAuto -> TypeVar (fresh_var' ())
      | ty -> traverse ty
    in
    fresh_type' (traverse_type fresh_type')
  in
  let fresh_params =
    List.map (fun (AParamDecl (ident, ty)) -> AParamDecl (ident, fresh_type ty))
  in
  let fresh_return = map_return_type fresh_type in
  let fresh_throws = map_throw_type (List.map fresh_type) in
  let fresh_expr =
    let fresh_expr' (traverse : expr -> expr) = function
      | TypeAsc (expr, ty) -> TypeAsc (traverse expr, fresh_type ty)
      | TypeCast (expr, ty) -> TypeCast (traverse expr, fresh_type ty)
      | Abstraction (params, expr) -> Abstraction (fresh_params params, expr)
      | TypeApplication (expr, tys) ->
          TypeApplication (expr, List.map fresh_type tys)
      | TryCastAs (e1, ty, pat, e2, e3) ->
          TryCastAs (traverse e1, fresh_type ty, pat, traverse e2, traverse e3)
      | Fold (ty, expr) -> Fold (fresh_type ty, traverse expr)
      | Unfold (ty, expr) -> Unfold (fresh_type ty, traverse expr)
      | expr -> traverse expr
    in
    fresh_expr' (traverse_expr fresh_expr')
  in
  List.map
    (function
      | DeclFun (annotations, ident, params, tyRet, throws, decls, expr) ->
          DeclFun
            ( annotations,
              ident,
              fresh_params params,
              fresh_return tyRet,
              fresh_throws throws,
              fresh_decls fresh_var decls,
              fresh_expr expr )
      | DeclFunGeneric
          (annotations, ident, tyArgs, params, tyRet, throws, decls, expr) ->
          DeclFunGeneric
            ( annotations,
              ident,
              tyArgs,
              fresh_params params,
              fresh_return tyRet,
              fresh_throws throws,
              fresh_decls fresh_var decls,
              fresh_expr expr )
      | DeclTypeAlias (ident, ty) -> DeclTypeAlias (ident, fresh_type ty)
      | DeclExceptionType ty -> DeclExceptionType (fresh_type ty)
      | DeclExceptionVariant (ident, ty) ->
          DeclExceptionVariant (ident, fresh_type ty))
    decls

let put_params (ctx : context) (params : paramDecl list) : context =
  List.iter (fun (AParamDecl (_, ty)) -> check_type ctx ty) params;
  List.map
    (fun (AParamDecl (StellaIdent name, ty)) -> Context.from_var name ty)
    params
  |> Context.concat |> Fun.flip Context.merge ctx

let rec used_vars (ty : typeT) : Set.Make(String).t =
  let module StringSet = Set.Make (String) in
  match ty with
  | TypeFun (tys, ty) ->
      List.fold_left
        (fun s ty -> StringSet.union s (used_vars ty))
        StringSet.empty (ty :: tys)
  | TypeForAll (idents, ty) ->
      let res = used_vars ty in
      let var =
        List.map (fun (StellaIdent name) -> name) idents |> StringSet.of_list
      in
      StringSet.diff res var
  (* | TypeRec of stellaIdent * typeT not supported *)
  | TypeSum (ty1, ty2) -> StringSet.union (used_vars ty1) (used_vars ty2)
  | TypeTuple tys ->
      List.fold_left
        (fun s ty -> StringSet.union s (used_vars ty))
        StringSet.empty tys
  | TypeRecord fields ->
      List.fold_left
        (fun s (ARecordFieldType (_, ty)) -> StringSet.union s (used_vars ty))
        StringSet.empty fields
  | TypeVariant fields ->
      List.fold_left
        (fun s (AVariantFieldType (_, typing)) ->
          match typing with
          | SomeTyping ty -> StringSet.union s (used_vars ty)
          | _ -> s)
        StringSet.empty fields
  | TypeList ty -> used_vars ty
  | TypeRef ty -> used_vars ty
  | TypeVar (StellaIdent name) -> StringSet.singleton name
  | _ -> StringSet.empty

let check_recur (var : string) (_in : typeT) : bool =
  let rec check_recur' (_in : typeT) : bool =
    match _in with
    | TypeFun (tys, ty) -> List.exists check_recur' tys || check_recur' ty
    | TypeForAll (idents, ty) ->
        if List.exists (fun (StellaIdent name) -> name = var) idents then false
        else check_recur' ty
    | TypeRec (StellaIdent name, ty) ->
        if name = var then false else check_recur' ty
    | TypeSum (tyL, tyR) -> check_recur' tyL || check_recur' tyR
    | TypeTuple tys -> List.exists check_recur' tys
    | TypeRecord fields ->
        List.exists
          (fun (ARecordFieldType (name, ty)) -> check_recur' ty)
          fields
    | TypeVariant fields ->
        List.exists
          (fun (AVariantFieldType (name, typing)) ->
            match typing with
            | SomeTyping ty -> check_recur' ty
            | NoTyping -> false)
          fields
    | TypeList ty -> check_recur' ty
    | TypeRef ty -> check_recur' ty
    | TypeVar (StellaIdent name) -> name = var
    | _ -> false
  in
  check_recur' _in

module type Context = sig
  val ambiguous : (unit -> typeT) -> typeT
  val exception_type : typeT option
  val is_subtyping : bool
  val eq : typeT -> typeT -> bool
  val unexpected_type : typeT -> typeT -> expr -> 'a
  val fresh_var : unit -> string
  val restrictions : (typeT * typeT) list ref
end

module Make (Ctx : Context) = struct
  let neq (ty1 : typeT) (ty2 : typeT) : bool = Ctx.eq ty1 ty2 |> not

  let rec substitute (from : string) (_to : typeT) (_in : typeT) =
    let rec s (_in : typeT) =
      match _in with
      | TypeFun (tys, ty) -> TypeFun (List.map s tys, s ty)
      | TypeForAll (idents, ty) ->
          if List.exists (fun (StellaIdent name) -> name = from) idents then _in
          else
            let module StringSet = Set.Make (String) in
            let used = used_vars _to in
            if
              List.exists
                (fun (StellaIdent name) -> StringSet.mem name used)
                idents
            then
              let ty', names =
                List.fold_left
                  (fun ((ty, names) : typeT * stellaIdent list)
                       (StellaIdent name) ->
                    let fresh_name = StellaIdent ("!" ^ Ctx.fresh_var ()) in
                    let fresh_ty = TypeVar fresh_name in
                    (substitute name fresh_ty ty, fresh_name :: names))
                  (ty, []) idents
              in
              TypeForAll (names, s ty')
            else TypeForAll (idents, s ty)
      | TypeRec (StellaIdent name, ty) ->
          if name = from then _in else TypeRec (StellaIdent name, s ty)
      | TypeSum (tyL, tyR) -> TypeSum (s tyL, s tyR)
      | TypeTuple tys -> TypeTuple (List.map s tys)
      | TypeRecord fields ->
          TypeRecord
            (List.map
               (fun (ARecordFieldType (name, ty)) ->
                 ARecordFieldType (name, s ty))
               fields)
      | TypeVariant fields ->
          TypeVariant
            (List.map
               (fun (AVariantFieldType (name, typing)) ->
                 AVariantFieldType
                   ( name,
                     match typing with
                     | SomeTyping ty -> SomeTyping (s ty)
                     | NoTyping -> NoTyping ))
               fields)
      | TypeList ty -> TypeList (s ty)
      | TypeRef ty -> TypeRef (s ty)
      | TypeVar (StellaIdent name) -> if name = from then _to else _in
      | _ -> _in
    in
    s _in

  let apply_type (tys : typeT list) (names : string list) (ty : typeT) : typeT =
    let names' = List.map (fun x -> StellaIdent x) names in
    if List.compare_lengths tys names <> 0 then
      incorrect_number_of_type_arguments (TypeForAll (names', ty)) tys
    else
      List.fold_left2 (fun ty from _to -> substitute from _to ty) ty names tys

  let unify (restrictions : (typeT * typeT) list) : typeT -> typeT =
    let rec unify' (restrictions : (typeT * typeT) list)
        (sigma : typeT -> typeT) : typeT -> typeT =
      match restrictions with
      | (ty1, ty2) :: restrictions' -> (
          match (ty1, ty2) with
          | TypeVar (StellaIdent name), TypeVar (StellaIdent name') ->
              if name = name' then unify' restrictions' sigma
              else
                let subs = substitute name (TypeVar (StellaIdent name')) in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | TypeVar (StellaIdent name), _ ->
              if check_recur name ty2 then occurs_check_infinite_type ty2
              else
                let subs = substitute name ty2 in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | _, TypeVar (StellaIdent name) ->
              if check_recur name ty1 then occurs_check_infinite_type ty1
              else
                let subs = substitute name ty1 in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
              let restrictions'' =
                List.concat
                  [
                    List.combine tyArgs1 tyArgs2;
                    [ (tyRet1, tyRet2) ];
                    restrictions';
                  ]
              in
              unify' restrictions'' sigma
          (* | TypeForAll not supported :shrug: *)
          (* | TypeRec not supported too *)
          | TypeSum (tyL1, tyR1), TypeSum (tyL2, tyR2) ->
              let restrictions'' =
                (tyL1, tyL2) :: (tyR1, tyR2) :: restrictions'
              in
              unify' restrictions'' sigma
          | TypeTuple tys1, TypeTuple tys2 ->
              let restrictions'' =
                List.concat [ List.combine tys1 tys2; restrictions' ]
              in
              unify' restrictions'' sigma
          | TypeRecord fields1, TypeRecord fields2 ->
              let fields1' =
                List.map
                  (fun (ARecordFieldType (StellaIdent name, ty')) ->
                    (name, ty'))
                  fields1
              in
              let fields2' =
                List.map
                  (fun (ARecordFieldType (StellaIdent name, ty')) ->
                    (name, ty'))
                  fields2
              in
              let rec convert (fields1 : (string * typeT) list)
                  (fields2 : (string * typeT) list)
                  ((fieldPairs, missingFields, extraFields) :
                    (typeT * typeT) list * string list * string list) =
                match fields1 with
                | (name, ty1) :: fields' -> (
                    match List.assoc_opt name fields2 with
                    | Some ty ->
                        convert fields'
                          (List.remove_assoc name fields2)
                          ((ty1, ty) :: fieldPairs, missingFields, extraFields)
                    | _ ->
                        convert fields'
                          (List.remove_assoc name fields2)
                          (fieldPairs, missingFields, name :: extraFields))
                | _ ->
                    ( fieldPairs,
                      List.concat
                        [ List.map (fun (a, _) -> a) fields2; missingFields ],
                      extraFields )
              in
              let fieldPairs, missingFields, extraFields =
                convert fields1' fields2' ([], [], [])
              in
              if List.compare_length_with extraFields 0 <> 0 then
                (* TODO: Version for unify *)
                unexpected_record_fields extraFields ty2 ConstUnit
              else if List.compare_length_with missingFields 0 <> 0 then
                missing_record_fields missingFields ty2 ConstUnit
              else unify' fieldPairs sigma
          (* | TypeVariant tricky not supported *)
          | TypeList ty1', TypeList ty2' ->
              unify' ((ty1', ty2') :: restrictions') sigma
          | TypeRef ty1', TypeRef ty2' ->
              unify' ((ty1', ty2') :: restrictions') sigma
          | _ ->
              (* TODO: Add unification error *)
              unexpected_type_for_expression ty1 ty2 ConstUnit)
      | [] -> sigma
    in
    unify' restrictions Fun.id

  let rec typecheck (ctx : context) (expr : expr) (ty : typeT) =
    (* print_endline
    ("Checking expr "
    ^ PrintStella.printTree PrintStella.prtExpr expr
    ^ " with type "
    ^ PrintStella.printTree PrintStella.prtTypeT ty); *)
    match (expr, ty) with
    | Sequence (e1, e2), _ ->
        typecheck ctx e1 TypeUnit;
        typecheck ctx e2 ty
    | Assign (e1, e2), _ -> (
        if neq TypeUnit ty then Ctx.unexpected_type ty TypeUnit expr
        else
          match infer ctx e1 with
          | TypeRef ty' -> typecheck ctx e2 ty'
          | ty' -> not_a_reference ty' e1)
    | If (eIf, eThen, eElse), _ ->
        typecheck ctx eIf TypeBool;
        typecheck ctx eThen ty;
        typecheck ctx eElse ty
    | Let (binders, expr'), _ ->
        (* TODO: check semantics *)
        let bindersCtx =
          List.map
            (fun (APatternBinding (p, expr'')) ->
              deconstruct_pattern_binder p (infer ctx expr''))
            binders
          |> Context.concat
        in
        let ctx' = Context.concat [ bindersCtx; ctx ] in
        typecheck ctx' expr' ty
    (* LetRec TODO *)
    | TypeAbstraction (tys, expr), TypeForAll (tysP, ty) ->
        if List.compare_lengths tys tysP <> 0 then
          Ctx.unexpected_type ty (infer ctx expr) expr
        else
          let ctx' =
            List.map (fun (StellaIdent a) -> a) tys
            |> List.fold_left Context.put_type ctx
          in
          let ty' =
            List.fold_left2
              (fun ty (StellaIdent from) _to ->
                substitute from (TypeVar _to) ty)
              ty tysP tys
          in
          typecheck ctx' expr ty'
    | TypeAbstraction _, _ -> Ctx.unexpected_type ty (infer ctx expr) expr
    | LessThan (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LessThanOrEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | GreaterThan (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | GreaterThanOrEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Equal (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | NotEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | TypeAsc (e1, ty'), _ ->
        if neq ty' ty then Ctx.unexpected_type ty ty' expr
        else (
          check_type ctx ty';
          typecheck ctx e1 ty')
    | Abstraction (params, expr'), TypeFun (tyParams, tyReturn) ->
        (* Check arity *)
        (* List.compare_lengths tyParams params = 0 *)
        List.iter2
          (fun ty (AParamDecl (ident, ty')) ->
            if neq ty' ty then
              unexpected_type_for_parameter ty ty' (to_param_decl ident ty)
            else ())
          tyParams params;
        let ctx' = put_params ctx params in
        check_type ctx' tyReturn;
        typecheck ctx' expr' tyReturn
    | Abstraction _, TypeTop -> infer ctx expr |> ignore
    | Abstraction _, _ -> unexpected_lambda ty expr
    | Variant (StellaIdent name, SomeExprData expr'), TypeVariant fieldTypes ->
        (* TODO: No expr data *)
        let rec find (fieldTypes : variantFieldType list) =
          match fieldTypes with
          | AVariantFieldType (StellaIdent name', SomeTyping ty') :: fieldTypes'
            ->
              if name = name' then ty' else find fieldTypes'
          | _ -> unexpected_variant_label ty name expr
        in
        let ty' = find fieldTypes in
        typecheck ctx expr' ty'
    | Variant _, TypeTop -> infer ctx expr |> ignore
    | Variant _, _ -> unexpected_variant ty expr
    | Match (_, []), _ -> illegal_empty_matching expr
    | Match (expr', cases), _ -> (
        let ty' = infer ctx expr' in
        List.iter
          (fun (AMatchCase (pat, expr'')) ->
            let ctx' =
              Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
            in
            typecheck ctx' expr'' ty)
          cases;
        let ps = List.map (fun (AMatchCase (p, _)) -> p) cases in
        match check_exhaustivness ps ty' with
        | Some expr'' -> nonexhaustive_match_patterns expr'' expr
        | None -> ())
    | List exprs, TypeList ty' ->
        List.iter (fun expr' -> typecheck ctx expr' ty') exprs
    | List [], TypeTop -> ()
    | List _, TypeTop -> infer ctx expr |> ignore
    | List _, _ -> unexpected_list ty expr
    | Add (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Subtract (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LogicOr (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool
    | Multiply (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Divide (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LogicAnd (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool
    | Ref expr', TypeRef ty' -> typecheck ctx expr' ty'
    | Ref expr', TypeTop -> typecheck ctx expr' ty
    | Ref _, _ -> Ctx.unexpected_type ty (infer ctx expr) expr
    | Deref _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Application _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | TypeApplication (expr, tys), _ -> (
        let ty' = infer ctx expr in
        match ty' with
        | TypeForAll (tys', tyRes) ->
            let tys' = List.map (fun (StellaIdent i) -> i) tys' in
            let ty'' = apply_type tys tys' tyRes in
            if neq ty'' ty then Ctx.unexpected_type ty ty'' expr
        | _ -> not_a_generic_function ty')
    | DotRecord _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | DotTuple _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Tuple exprs, TypeTuple tyExprs ->
        if List.compare_lengths exprs tyExprs <> 0 then
          unexpected_tuple_length (List.length tyExprs) (List.length exprs) expr
        else
          List.fold_left
            (fun _ (expr, ty) -> typecheck ctx expr ty)
            ()
            (List.combine exprs tyExprs)
    | Tuple _, TypeTop -> infer ctx expr |> ignore
    | Tuple _, _ -> unexpected_tuple ty expr
    | Record fields, TypeRecord fieldTypes ->
        let fields' =
          List.map
            (fun (ABinding (StellaIdent name, expr')) -> (name, expr'))
            fields
        in
        let rec findDupFields (fields : (string * _) list)
            (dupFields : string list) =
          match fields with
          | (name, _) :: fields' ->
              let dupFields' =
                if List.mem_assoc name fields' && not (List.mem name dupFields)
                then name :: dupFields
                else dupFields
              in
              findDupFields fields' dupFields'
          | _ -> dupFields
        in
        let dupFields = findDupFields fields' [] in
        if List.compare_length_with dupFields 0 <> 0 then
          duplicate_record_fields dupFields expr
        else
          let fieldTypes' =
            List.map
              (fun (ARecordFieldType (StellaIdent name, ty')) -> (name, ty'))
              fieldTypes
          in
          let rec convert (fields : (string * expr) list)
              (types : (string * typeT) list)
              ((fieldExpr, missingFields, extraFields) :
                (expr * typeT) list * string list * string list) =
            match fields with
            | (name, expr) :: fields' -> (
                match List.assoc_opt name types with
                | Some ty ->
                    convert fields'
                      (List.remove_assoc name types)
                      ((expr, ty) :: fieldExpr, missingFields, extraFields)
                | _ ->
                    convert fields'
                      (List.remove_assoc name types)
                      (fieldExpr, missingFields, name :: extraFields))
            | _ ->
                ( fieldExpr,
                  List.concat
                    [ List.map (fun (a, _) -> a) types; missingFields ],
                  extraFields )
          in
          let fieldExpr, missingFields, extraFields =
            convert fields' fieldTypes' ([], [], [])
          in
          if List.compare_length_with extraFields 0 <> 0 && not Ctx.is_subtyping
          then unexpected_record_fields extraFields ty expr
          else if List.compare_length_with missingFields 0 <> 0 then
            missing_record_fields missingFields ty expr
          else List.iter (fun (expr', ty') -> typecheck ctx expr' ty') fieldExpr
    | Record _, TypeTop -> infer ctx expr |> ignore
    | Record _, _ -> unexpected_record ty expr
    | ConsList (e1, e2), TypeList ty' ->
        typecheck ctx e1 ty';
        typecheck ctx e2 ty
    | ConsList _, _ -> unexpected_list ty expr
    | Head _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Tail _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | IsEmpty _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Panic, _ -> ()
    | Throw expr', _ -> (
        match Ctx.exception_type with
        | Some ty' -> typecheck ctx expr' ty'
        | None -> exception_type_not_declared expr)
    | TryCatch (e1, pat, e2), _ ->
        typecheck ctx e1 ty;
        let exception_type =
          match Ctx.exception_type with
          | Some ty -> ty
          | None -> exception_type_not_declared expr
        in
        let ctx' =
          Context.concat [ deconstruct_pattern_binder pat exception_type ]
        in
        typecheck ctx' e2 ty
    | TryWith (e1, e2), _ ->
        typecheck ctx e1 ty;
        typecheck ctx e2 ty
    | Inl expr', TypeSum (tyL, _) -> typecheck ctx expr' tyL
    | Inl expr', TypeTop -> typecheck ctx expr' TypeTop
    | Inl _, _ -> unexpected_injection ty expr
    | Inr expr', TypeSum (_, tyR) -> typecheck ctx expr' tyR
    | Inr expr', TypeTop -> typecheck ctx expr' TypeTop
    | Inr _, _ -> unexpected_injection ty expr
    | Succ expr', _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx expr' TypeNat
    | LogicNot expr', _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx expr' TypeBool
    | Pred expr', _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx expr' TypeNat
    | IsZero expr', _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx expr' TypeNat
    | Fix _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr
    | NatRec (eN, eZ, eS), _ ->
        typecheck ctx eN TypeNat;
        typecheck ctx eZ ty;
        typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)))
    | ConstTrue, _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr else ()
    | ConstFalse, _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr else ()
    | ConstUnit, _ ->
        if neq TypeUnit ty then Ctx.unexpected_type ty TypeUnit expr else ()
    | ConstInt _, _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr else ()
    | ConstMemory _, TypeRef _ -> ()
    | ConstMemory _, TypeTop -> ()
    | ConstMemory _, _ -> unexpected_memory_address ty expr
    | Var (StellaIdent name), _ -> (
        match Context.get ctx name with
        | None -> undefined_variable name expr
        | Some ty' -> if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
        )
    | a, _ ->
        print_endline (ShowStella.show (ShowStella.showExpr a));
        not_implemented "typecheck"

  and infer (ctx : context) (expr : expr) : typeT =
    match expr with
    | Sequence (e1, e2) ->
        typecheck ctx e1 TypeUnit;
        infer ctx e2
    | Assign (e1, e2) ->
        (match infer ctx e1 with
        | TypeRef ty' -> typecheck ctx e2 ty'
        | ty' -> not_a_reference ty' e1);

        TypeUnit
    | If (eIf, eThen, eElse) ->
        typecheck ctx eIf TypeBool;
        let ty = infer ctx eThen in
        typecheck ctx eElse ty;
        ty
    | Let (binders, expr') ->
        (* TODO check semantics of let a = ..., b = a <- impossible in such tc *)
        let bindersCtx =
          List.map
            (fun (APatternBinding (p, expr'')) ->
              deconstruct_pattern_binder p (infer ctx expr''))
            binders
          |> Context.concat
        in
        let ctx' = Context.concat [ bindersCtx; ctx ] in
        infer ctx' expr'
    (* | LetRec of patternBinding list * expr TODO *)
    | TypeAbstraction (tys, expr) ->
        let ctx' =
          List.map (fun (StellaIdent a) -> a) tys
          |> List.fold_left Context.put_type ctx
        in
        infer ctx' expr
    | LessThan (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | LessThanOrEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | GreaterThan (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | GreaterThanOrEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | Equal (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | NotEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | TypeAsc (expr', ty) ->
        check_type ctx ty;
        typecheck ctx expr' ty;
        ty
    | Abstraction (params, expr') ->
        let ctx' = put_params ctx params in
        let tyReturn = infer ctx' expr' in
        TypeFun (List.map (fun (AParamDecl (_, ty)) -> ty) params, tyReturn)
    | Variant (ident, data) ->
        if Ctx.is_subtyping then
          TypeVariant
            [
              AVariantFieldType
                ( ident,
                  match data with
                  | SomeExprData data' -> SomeTyping (infer ctx data')
                  | NoExprData -> NoTyping );
            ]
        else ambiguous_variant_type expr
    | Match (_, []) -> illegal_empty_matching expr
    | Match (expr', AMatchCase (pat, expr'') :: cases) ->
        let ty' = infer ctx expr' in
        let tyRes =
          let ctx' =
            Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
          in
          infer ctx' expr''
        in
        List.iter
          (fun (AMatchCase (pat, expr'')) ->
            let ctx' =
              Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
            in
            typecheck ctx' expr'' tyRes)
          cases;
        let ps =
          List.map
            (fun (AMatchCase (p, _)) -> p)
            (AMatchCase (pat, expr'') :: cases)
        in
        (match check_exhaustivness ps ty' with
        | Some expr'' -> nonexhaustive_match_patterns expr'' expr
        | None -> ());
        tyRes
    | List (expr' :: exprs) ->
        let ty = infer ctx expr' in
        List.iter (fun expr'' -> typecheck ctx expr'' ty) exprs;
        TypeList ty
    | List [] -> TypeList (ambiguous_list' expr |> Ctx.ambiguous)
    | Add (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | Subtract (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | LogicOr (e1, e2) ->
        typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool;
        TypeBool
    | Multiply (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | Divide (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | LogicAnd (e1, e2) ->
        typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool;
        TypeBool
    | Ref expr' -> TypeRef (infer ctx expr')
    | Deref expr' -> (
        match infer ctx expr' with
        | TypeRef ty' -> ty'
        | ty' -> not_a_reference ty' expr)
    | Application (eFun, eArgs) -> (
        (* TODO: Incorrect arity *)
        let tyFun = infer ctx eFun in
        match tyFun with
        | TypeFun (tyArgs, tyReturn) ->
            List.iter
              (fun (eArg, tyArg) -> typecheck ctx eArg tyArg)
              (List.combine eArgs tyArgs);
            tyReturn
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let fresh_args =
                List.map
                  (fun e ->
                    let ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
                    typecheck ctx e ty;
                    ty)
                  eArgs
              in
              let fresh_ret = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeFun (fresh_args, fresh_ret), tyFun) :: !Ctx.restrictions;
              fresh_ret)
            else not_a_function tyFun expr
        | _ -> not_a_function tyFun expr)
    | TypeApplication (expr, tys) -> (
        let ty' = infer ctx expr in
        match ty' with
        | TypeForAll (tys', tyRes) ->
            let tys' = List.map (fun (StellaIdent i) -> i) tys' in
            let ty'' = apply_type tys tys' tyRes in
            ty''
        | _ -> not_a_generic_function ty')
    | DotRecord (expr', StellaIdent name) -> (
        let tyRec = infer ctx expr' in
        match tyRec with
        | TypeRecord fields ->
            let rec find_field (fields : recordFieldType list) =
              match fields with
              | ARecordFieldType (StellaIdent name', tyField) :: fields' ->
                  if name' = name then tyField else find_field fields'
              | [] -> unexpected_field_access tyRec name expr
            in
            find_field fields
        | TypeVar (StellaIdent name') ->
            if String.starts_with ~prefix:"?" name' then (
              let fresh_ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                ( TypeRecord [ ARecordFieldType (StellaIdent name, fresh_ty) ],
                  tyRec )
                :: !Ctx.restrictions;
              fresh_ty)
            else not_a_record tyRec expr
        | _ -> not_a_record tyRec expr)
    | DotTuple (expr, n) -> (
        let ty = infer ctx expr in
        match ty with
        | TypeTuple tyTuple ->
            if List.compare_length_with tyTuple n < 0 || n <= 0 then
              tuple_index_out_of_bounds ty n expr
            else List.nth tyTuple (n - 1)
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let ty1 = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              let ty2 = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeTuple [ ty1; ty2 ], ty) :: !Ctx.restrictions;
              List.nth [ ty1; ty2 ] (n - 1))
            else not_a_tuple ty expr
        | _ -> not_a_tuple ty expr)
    | Tuple exprs -> TypeTuple (List.map (infer ctx) exprs)
    | Record bindings ->
        let dup =
          List.map (fun (ABinding (StellaIdent name, _)) -> name) bindings
          |> find_dup
        in
        if List.compare_length_with dup 0 <> 0 then
          duplicate_record_fields dup expr
        else
          TypeRecord
            (List.map
               (fun (ABinding (ident, expr)) ->
                 ARecordFieldType (ident, infer ctx expr))
               bindings)
    | ConsList (eHead, eTail) ->
        let ty = infer ctx eHead in
        typecheck ctx eTail (TypeList ty);
        TypeList ty
    | Head expr' -> (
        let ty = infer ctx expr' in
        match ty with TypeList tyElem -> tyElem | _ -> not_a_list ty expr)
    | IsEmpty expr' -> (
        let ty = infer ctx expr' in
        match ty with TypeList _ -> TypeBool | _ -> not_a_list ty expr)
    | Tail expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeList tyElem -> TypeList tyElem
        | _ -> not_a_list ty expr)
    | Panic -> ambiguous_panic_type' expr |> Ctx.ambiguous
    | Throw expr' ->
        let tyRes = ambiguous_throw_type' expr |> Ctx.ambiguous in
        (match Ctx.exception_type with
        | Some ty' -> typecheck ctx expr' ty'
        | None -> exception_type_not_declared expr);
        tyRes
    | TryCatch (e1, pat, e2) ->
        let ty = infer ctx e1 in
        let exception_type =
          match Ctx.exception_type with
          | Some ty -> ty
          | None -> exception_type_not_declared expr
        in
        let ctx' =
          Context.concat [ deconstruct_pattern_binder pat exception_type ]
        in
        typecheck ctx' e2 ty;
        ty
    | TryWith (e1, e2) ->
        let ty = infer ctx e1 in
        typecheck ctx e2 ty;
        ty
    | Inl expr' ->
        let right = ambiguous_sum_type' expr |> Ctx.ambiguous in
        let left = infer ctx expr' in
        TypeSum (left, right)
    | Inr expr' ->
        let left = ambiguous_sum_type' expr |> Ctx.ambiguous in
        let right = infer ctx expr' in
        TypeSum (left, right)
    | Succ expr' ->
        typecheck ctx expr' TypeNat;
        TypeNat
    | LogicNot expr' ->
        typecheck ctx expr' TypeBool;
        TypeBool
    | Pred expr' ->
        typecheck ctx expr' TypeNat;
        TypeNat
    | IsZero expr' ->
        typecheck ctx expr' TypeNat;
        TypeBool
    | Fix expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeFun ([ tyArg ], tyRet) ->
            if neq tyArg tyRet || neq tyRet tyArg then
              Ctx.unexpected_type
                (TypeFun ([ tyArg ], tyArg))
                (TypeFun ([ tyArg ], tyRet))
                expr
            else tyArg
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let fresh_ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeFun ([ fresh_ty ], fresh_ty), ty) :: !Ctx.restrictions;
              fresh_ty)
            else not_a_function ty expr
        | _ -> not_a_function ty expr)
    | NatRec (eN, eZ, eS) ->
        typecheck ctx eN TypeNat;
        let ty = infer ctx eZ in
        typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)));
        ty
    | ConstTrue -> TypeBool
    | ConstFalse -> TypeBool
    | ConstUnit -> TypeUnit
    | ConstInt _ -> TypeNat
    | ConstMemory _ -> TypeRef (ambiguous_reference_type' expr |> Ctx.ambiguous)
    | Var (StellaIdent name) -> (
        match Context.get ctx name with
        | Some ty -> ty
        | None -> undefined_variable name expr)
    | _ -> not_implemented "infer"
end

let typecheckProgram (program : program) =
  let extensions = get_extensions' program |> Extensions.to_record in
  let _, decls = get_program' program in
  let ambiguous =
    if extensions.ambiguous_type_as_bottom then fun _ -> TypeBottom
    else fun f -> f ()
  in
  let exception_type =
    if extensions.open_variant_exceptions then
      let variants =
        List.concat_map
          (function
            | DeclExceptionVariant (ident, ty) ->
                [ AVariantFieldType (ident, SomeTyping ty) ]
            | _ -> [])
          decls
      in
      if List.compare_length_with variants 0 = 0 then None
      else Some (TypeVariant variants)
    else
      List.find_map
        (fun decl ->
          match decl with DeclExceptionType ty -> Some ty | _ -> None)
        decls
  in
  let is_subtyping = extensions.structural_subtyping in
  let is_reconstruction = extensions.type_reconstruction in
  let restrictions = ref [] in
  let eq = if is_subtyping then subtype else make_eq restrictions in
  let unexpected_type =
    if is_subtyping then unexpected_subtype else unexpected_type_for_expression
  in
  let count = ref 0 in
  let fresh_var () : string =
    count := !count + 1;
    Printf.sprintf "?T%d" !count
  in
  let module M = Make (struct
    let ambiguous = ambiguous
    let exception_type = exception_type
    let is_subtyping = is_subtyping
    let eq = eq
    let unexpected_type = unexpected_type
    let fresh_var = fresh_var
    let restrictions = restrictions
  end) in
  let typecheck = M.typecheck in
  let decls = fresh_decls fresh_var decls in
  let ctx =
    List.fold_left
      (fun a b ->
        match b with
        | DeclFun (_, StellaIdent name, params, SomeReturnType tyReturn, _, _, _)
          ->
            let tyParams =
              List.map (fun (AParamDecl (name, tyParam)) -> tyParam) params
            in
            Context.put a name (TypeFun (tyParams, tyReturn))
        | DeclFunGeneric
            (_, StellaIdent name, tyP, params, SomeReturnType tyReturn, _, _, _)
          ->
            let tyParams =
              List.map (fun (AParamDecl (name, tyParam)) -> tyParam) params
            in
            Context.put a name (TypeForAll (tyP, TypeFun (tyParams, tyReturn)))
        | DeclExceptionType _ -> a
        | DeclExceptionVariant _ -> a
        | _ -> not_implemented "typecheckProgram")
      Context.empty decls
  in
  check_main ctx;
  List.iter
    (function
      (* TODO: Add decl support *)
      | DeclFun ([], _, params, SomeReturnType tyReturn, NoThrowType, [], expr)
        ->
          let ctx' = put_params ctx params in
          check_type ctx tyReturn;
          typecheck ctx' expr tyReturn
      | DeclFunGeneric
          ([], _, tyP, params, SomeReturnType tyReturn, NoThrowType, [], expr)
        ->
          let ctx' =
            List.map (fun (StellaIdent ident) -> ident) tyP
            |> List.fold_left Context.put_type ctx
          in
          let ctx' = put_params ctx' params in
          check_type ctx' tyReturn;
          typecheck ctx' expr tyReturn
      | DeclExceptionType _ -> ()
      | DeclExceptionVariant _ -> ()
      | _ -> not_implemented "typecheckProgram")
    decls;
  if is_reconstruction then
    let sigma = M.unify !restrictions in
    ignore sigma
  else ()
