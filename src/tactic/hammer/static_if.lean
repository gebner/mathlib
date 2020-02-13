import tactic.core
universe u

namespace tactic.interactive
setup_tactic_parser
open tactic

namespace static_if

meta class branchable {α : Sort u} (a : α) :=
(eval_cond : tactic bool)

meta instance decidable (p : Prop) [decidable p] : branchable p :=
⟨_, pure p⟩

meta instance tactic (t : tactic bool) : branchable t :=
⟨_, t⟩

meta instance bool (t : bool) : branchable t :=
⟨_, pure t⟩

end static_if

meta def static_if
  (cond : parse texpr)
  (_ : parse $ tk "then")
  (a : parse texpr)
  (_ : parse $ tk "else")
  (b : parse texpr)
  : tactic unit := do
cond ← to_expr cond,
brnchbl_inst ← mk_mapp ``tactic.interactive.static_if.branchable [none, cond]
    >>= mk_instance
  <|> (do cond_ty ← infer_type cond >>= pp,
          fail $ to_fmt "cannot branch on condition of type " ++ cond_ty),
cond ← mk_mapp ``tactic.interactive.static_if.branchable.eval_cond
  [none, cond, brnchbl_inst],
cond ← eval_expr' (tactic bool) cond,
cond ← cond,
if cond then
  exact a
else
  exact b

end tactic.interactive
