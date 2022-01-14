(* This module is implemented based on the Algorithmic PolyKinds system
   introduced in Kind Inference for Datatypes. The original paper and its
   technical supplement can be found in these links:

   https://richarde.dev/papers/2020/kind-inference/kind-inference.pdf

   https://arxiv.org/pdf/1911.06153.pdf *)
open Sulfur_ast

let instantiate (_gamma : Context.t) ((_T, _K) : Type.t * Type.t) (_K : Type.t)
    : (Context.t * Type.t, Sulfur_errors.t) result =
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

and unify (_gamma : Context.t) (_A : Type.t) (_B : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  failwith "unify: undefined"

and promote (_gamma : Context.t) (_a : string) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "promote: undefined"
