val instantiate :
     Context.t
  -> Sulfur_ast.Type.t * Sulfur_ast.Type.t
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result

val check :
     Context.t
  -> Sulfur_ast.Type.t
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result

val infer :
     Context.t
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result

val infer_apply :
     Context.t
  -> Sulfur_ast.Type.t * Sulfur_ast.Type.t
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result

val infer_elaborated :
     Context.t
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result

val unify :
     Context.t
  -> Sulfur_ast.Type.t
  -> Sulfur_ast.Type.t
  -> (Context.t, Sulfur_errors.t) result

val promote :
     Context.t
  -> string
  -> Sulfur_ast.Type.t
  -> (Context.t * Sulfur_ast.Type.t, Sulfur_errors.t) result
