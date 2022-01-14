(* This module is implemented based on the Algorithmic PolyKinds system
   introduced in Kind Inference for Datatypes. The original paper and its
   technical supplement can be found in these links:

   https://richarde.dev/papers/2020/kind-inference/kind-inference.pdf

   https://arxiv.org/pdf/1911.06153.pdf *)
open Sulfur_ast
open Sulfur_errors.Let

let rec instantiate (_gamma : Context.t) ((_T, _K) : Type.t * Type.t)
    (_K : Type.t) : (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "instantiate: undefined"

and check (_gamma : Context.t) (_T : Type.t) (_K : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "check: undefined"

and infer (_gamma : Context.t) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "infer: undefined"

and infer_apply (_gamma : Context.t) ((_T, _K) : Type.t * Type.t) (_K : Type.t)
    : (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "infer_apply: undefined"

and infer_elaborated (_gamma : Context.t) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "infer_elaborated: undefined"

and unify (ctx : Context.t) (_A : Type.t) (_B : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  match (_A, _B) with
  (* A-U-APP *)
  | Apply (p1, p2), Apply (p3, p4) ->
      let* gamma = unify ctx p1 p3 in
      unify gamma (Context.apply gamma p2) (Context.apply gamma p4)
  (* A-U-KAPP *)
  | KindApply (p1, p2), KindApply (p3, p4) ->
      let* gamma = unify ctx p1 p3 in
      unify gamma (Context.apply gamma p2) (Context.apply gamma p4)
  (* A-U-REFL-TT *)
  | _A, _B when Type.equal _A _B -> Ok ctx
  (* A-U-KVARL-TT *)
  | Unsolved a, p1 -> unify_unsolved ctx a p1
  (* A-U-KVARR-TT *)
  | p1, Unsolved a -> unify_unsolved ctx a p1
  (* FALLTHROUGH *)
  | _ -> failwith "unify: FALLTHROUGH: todo: raise a more appropriate error"

and promote (ctx : Context.t) (a : string) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  match _T with
  | Unsolved b ->
      let b_appears_first =
        let discard_up_to_a (ctx : Context.t) : Context.t =
          let rec aux = function
            | [] -> []
            | Context.Element.Unsolved (a', _) :: t when String.equal a a' -> t
            | _ :: t -> aux t
          in
          aux ctx
        in
        let b_is_member (ctx : Context.t) : bool =
          let rec aux = function
            | [] -> false
            | Context.Element.Unsolved (b', _) :: _ when String.equal b b' ->
                true
            | _ :: t -> aux t
          in
          aux ctx
        in
        b_is_member (discard_up_to_a ctx)
      in
      if b_appears_first
      then Ok (ctx, _T)
      else failwith "promote: todo: make sure to promote b's kind."
  | _ -> Ok (ctx, _T)

and unify_unsolved (ctx : Context.t) (a : string) (p1 : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  let* ctx, p2 = promote ctx a p1 in
  let* ctx2, w1, ctx1 =
    let rec aux (l : Context.t) :
        Context.t -> (Context.t * Type.t * Context.t, Sulfur_errors.t) result =
      function
      | [] -> failwith "unify_unsolved: todo: raise a more appropriate error"
      | h :: t -> (
          match h with
          | Context.Element.Unsolved (a', k) when String.equal a a' ->
              Ok (List.rev l, k, t)
          | _ -> aux (h :: l) t)
    in
    aux [] ctx
  in
  let* ctx1, w2 = infer_elaborated ctx1 p2 in
  let* ctx3 = unify ctx1 (Context.apply ctx1 w1) w2 in
  Ok (List.append ctx2 (Context.Element.Solved (a, p2) :: ctx3))
