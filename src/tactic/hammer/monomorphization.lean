import data.analysis.filter
tactic.hammer.fo_translation

meta def expr.consts_and_local_consts (e : expr) : list expr :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e _ s,
match e with
| e@(expr.const n _) := s.insert n
| _ := s
end

namespace hammer

open expr tactic

meta def num_mono_args : expr → ℕ
| (expr.pi pp_n bi d t) :=
  let n' := num_mono_args t in
  if n' > 0 then
    n' + 1
  else if t.has_var_idx 0 ∨ bi = binder_info.inst_implicit then
    1
  else
    0
| _ := 0

end hammer
