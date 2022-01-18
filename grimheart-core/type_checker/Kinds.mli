val instantiate :
     Context.t
  -> Grimheart_ast.Type.t * Grimheart_ast.Type.t
  -> Grimheart_ast.Type.t
  -> (Context.t * Grimheart_ast.Type.t, Grimheart_core_errors.t) result

val check :
     Context.t
  -> Grimheart_ast.Type.t
  -> Grimheart_ast.Type.t
  -> (Context.t * Grimheart_ast.Type.t, Grimheart_core_errors.t) result

val infer :
     Context.t
  -> Grimheart_ast.Type.t
  -> ( Context.t * Grimheart_ast.Type.t * Grimheart_ast.Type.t
     , Grimheart_core_errors.t )
     result

val infer_apply :
     Context.t
  -> Grimheart_ast.Type.t * Grimheart_ast.Type.t
  -> Grimheart_ast.Type.t
  -> ( Context.t * Grimheart_ast.Type.t * Grimheart_ast.Type.t
     , Grimheart_core_errors.t )
     result

val elaborate :
     Context.t
  -> Grimheart_ast.Type.t
  -> (Grimheart_ast.Type.t, Grimheart_core_errors.t) result

val subsumes :
     Context.t
  -> Grimheart_ast.Type.t
  -> Grimheart_ast.Type.t
  -> (Context.t, Grimheart_core_errors.t) result

val unify :
     Context.t
  -> Grimheart_ast.Type.t
  -> Grimheart_ast.Type.t
  -> (Context.t, Grimheart_core_errors.t) result

val promote :
     Context.t
  -> string
  -> Grimheart_ast.Type.t
  -> (Context.t * Grimheart_ast.Type.t, Grimheart_core_errors.t) result
