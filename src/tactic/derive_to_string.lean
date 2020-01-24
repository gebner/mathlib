import init.category.combinators meta.expr

namespace tactic

namespace derive_to_string

def fmt_string (fn : string) (args : list string) : string :=
if args = [] then fn else
" ".intercalate (fn :: args.map (λ a, "(" ++ a ++ ")"))

meta def fmt_format (fn : string) (args : list format) : format :=
if args.empty then to_fmt fn else
(args.foldl (λ acc arg : format, acc ++ format.line ++ "(" ++ arg++ ")") (to_fmt fn)).group.nest 1

meta def fmt_tactic_format (fn : string) (args : list (tactic format)) : tactic format := do
fmt_format fn <$> monad.sequence args

meta def tactic_format_of_string (s : string) : tactic format :=
pure s

def string_of_string : string → string := id

end derive_to_string
open derive_to_string

private meta def combine_args_and_ihs_core : list (expr × bool) → list expr → list (expr × option expr)
| ((a,ff)::as) ihs := (a, none) :: combine_args_and_ihs_core as ihs
| ((a,tt)::as) (ih::ihs) := (a, ih) :: combine_args_and_ihs_core as ihs
| _ _ := []

private meta def combine_args_and_ihs (ity : expr) (args : list expr) : tactic (list (expr × option expr)) := do
args ← args.mmap (λ a, do
  ta ← infer_type a,
  let is_rec_arg : bool := ta.get_app_fn.const_name = ity.get_app_fn.const_name,
  pure (a, is_rec_arg)),
let rec_args := args.filter (λ a, a.2),
let ihs := (args.reverse.take rec_args.length).reverse.map prod.fst,
let args := (args.reverse.drop rec_args.length).reverse,
pure $ combine_args_and_ihs_core args ihs

meta def mk_to_string_instance_core (arg : expr) (lift fmt of_string : name) : tactic unit := do
string_ty ← target,
tx ← infer_type arg,
ctrs ← induction arg,
ctrs.mmap' $ λ ⟨ctr, args, _⟩, do
let ctr := ctr.last,
args ← combine_args_and_ihs tx args,
applyc fmt,
exact (reflect ctr),
args.mmap' (λ arg, do
  applyc ``list.cons,
  match arg with
  | (arg, none) := (mk_mapp lift [none, none, some arg] >>= exact) <|>
      (mk_mapp of_string [reflect "_"] >>= exact) <|> (trace_state >> fail of_string)
  | (_, some ih) := exact ih
  end),
applyc ``list.nil,
skip

meta def mk_to_string_instance : tactic unit := do
tgt ← target,
match tgt with
| `(has_to_string %%_) := do
    x ← constructor >> intro1,
    mk_to_string_instance_core x ``to_string ``fmt_string ``string_of_string
| `(has_to_tactic_format %%_) := do
    x ← constructor >> intro1,
    mk_to_string_instance_core x ``tactic.pp ``fmt_tactic_format ``tactic_format_of_string
| `(has_to_format %%_) := do
    x ← constructor >> intro1,
    mk_to_string_instance_core x ``to_fmt ``fmt_format ``format.of_string
| `(has_repr %%_) := do
    x ← constructor >> intro1,
    mk_to_string_instance_core x ``repr ``fmt_string ``string_of_string
| _ := do tgt ← pp tgt,
  fail $ to_fmt "mk_to_string_instance: unsupported goal: " ++ tgt
end

@[derive_handler] meta def derive_to_string : derive_handler :=
instance_derive_handler ``has_to_string mk_to_string_instance

@[derive_handler] meta def derive_to_format : derive_handler :=
instance_derive_handler ``has_to_format mk_to_string_instance

@[derive_handler] meta def derive_repr : derive_handler :=
instance_derive_handler ``has_repr mk_to_string_instance

@[derive_handler] meta def derive_to_tactic_format : derive_handler :=
instance_derive_handler ``has_to_tactic_format mk_to_string_instance

end tactic

attribute [derive [has_to_string, has_to_format, has_repr, has_to_tactic_format]]
  reducibility_hints declaration
