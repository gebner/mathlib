import data.list.defs meta.expr tactic.core
import data.list.sort
import tactic.hammer.static_if

attribute [inline] bool.decidable_eq decidable.to_bool

@[inline]
meta def name.has_suffix (s : string) : name → bool
| (name.mk_string s' _) := s = s'
| _ := false

namespace hammer

open native tactic feature_search

private meta def ignored_consts : name_set :=
name_set.of_list [ ``Exists, ``and, ``or, ``iff, ``eq, ``heq, name.anonymous ]

private meta def sunfold_name := "_sunfold"
private meta def main_name := "_main"

meta def is_ignored_const (n : name) : bool :=
n.has_suffix sunfold_name ∨ n.has_suffix main_name ∨ ignored_consts.contains n

-- #eval feature_search.feature_vec.of_thm ``add_comm >>= trace

meta def doc_weight (doc : feature_vec) (dfm : rb_map feature nat) : nat :=
(doc.to_list.map (λ f, dfm.size / (dfm.find f).get_or_else 0)).sum

meta def select_for_goal (e : environment) (g : expr) (cfg : feature_cfg := {}) : list $ name × float :=
let lems := e.get_trusted_decls.filter $ λ d,
  ¬ d.to_name.is_internal ∧
  ¬ is_ignored_const d.to_name ∧
  ¬ d.is_auto_generated e in
let lems := lems.map (λ d, (d.to_name, feature_vec.of_expr e d.type cfg)) in
let lems := lems.filter (λ l, ¬ l.2.to_list.empty) in
let dfm := feature_stats.of_feature_vecs (lems.map prod.snd) in
let goal_fv := feature_vec.of_expr e g cfg in
let ws := lems.map $ λ ⟨n, fv⟩, (n, dfm.cosine_similarity goal_fv fv) in
let ws := ws.filter $ λ x, x.2 > 0 in
let ws := ws.merge_sort $ λ a b, a.2 > b.2 in
ws

meta def select_for_goal' (g : expr) (cfg : feature_cfg := {}) : tactic (list (name × float)) := do
env ← get_env,
pure $ select_for_goal env g cfg

end hammer

namespace tactic

meta def reverted_target : tactic expr :=
retrieve $ do unfreeze_local_instances, revert_all, target >>= instantiate_mvars

namespace interactive

meta def feature_search (max := 10) (cfg : feature_search.feature_cfg := {}) : tactic unit := do
goal ← reverted_target,
env ← get_env,
let lems := hammer.select_for_goal env goal cfg,
(lems.take max).mmap' trace

end interactive
end tactic

set_option profiler true

-- example : ∀ x y : nat, x + y = y + x := by feature_search 100; sorry
