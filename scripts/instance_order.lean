import tactic.core tactic.hammer.monomorphization data.real.basic analysis.calculus.deriv

open tactic

meta def all_instances : tactic (list name) := do
e ← get_env,
let ds := e.get_trusted_decls,
let ds := ds.map declaration.to_name,
ds.mfilter is_instance

meta def edges_of_type (ty : expr) : tactic (list (name × name)) := do
(args, head) ← get_pi_binders ty,
expr.const head_class _ ← pure head.get_app_fn | pure [],
tt ← has_attribute' `class head_class | pure [],
arg_classes ← (args.map (λ a : binder, a.type.get_app_fn.const_name))
  .mfilter (has_attribute' `class),
pure $ do ac ← arg_classes.reverse.take 1, guard (ac ≠ head_class), pure (ac, head_class)

meta def edges (inst : name) : tactic (list (name × name)) := do
decl ← get_decl inst,
let ty := decl.type,
edges_of_type ty

meta def all_edges : tactic (list (name × name)) := do
insts ← all_instances,
list.dup_native <$> list.join <$> insts.mmap edges

#eval do
es ← all_edges,
trace "digraph instances {",
let to_string (n : name) :=
  ((n.to_string.to_list).map (λ c,
    if c = '.' ∨ c = '\'' then '_' else c)).as_string,
es.mmap' (λ ⟨a,b⟩, trace $ "  " ++ to_string a ++ " -> " ++ to_string b ++ ";"),
trace "}"

meta def hyperedges_of_type (ty: expr)  : tactic (option $ name × list name) := do
(args, head) ← get_pi_binders ty,
expr.const head_class _ ← pure head.get_app_fn | pure none,
tt ← has_attribute' `class head_class | pure none,
arg_classes ← (args.map (λ a : binder, a.type.get_app_fn.const_name))
  .mfilter (has_attribute' `class),
pure (head_class, arg_classes)

meta def all_hyperedges : tactic (list $ name × list name) := do
insts ← all_instances,
inst_tys ← insts.mmap (λ i, declaration.type <$> get_decl i),
list.join <$> list.map option.to_list <$> inst_tys.mmap hyperedges_of_type

#eval all_hyperedges >>= trace
