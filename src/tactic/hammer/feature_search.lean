import data.list.defs meta.expr tactic.core

local attribute [inline] name.has_lt name.lt.decidable_rel

meta def expr.constants_set (e : expr) : name_set :=
e.fold mk_name_set $ λ e _ s,
match e with
| (expr.const n _) := s.insert n
| _ := s
end

namespace hammer

open native tactic

@[reducible]
def feature := name

@[reducible]
meta def feature_vec :=
name_set

private def ignored_consts :=
[ ``Exists, ``and, ``or, ``iff, ``eq, ``heq ]

meta def mk_blacklist : tactic (rb_set name) := do
e ← get_env,
ds ← e.get_trusted_decls.mfilter (λ d, is_instance d.to_name),
cs ← attribute.get_instances `class,
pure $ rb_map.set_of_list $ ignored_consts ++ cs ++ ds.map (λ d, d.to_name)

meta def features_of_decl' (blacklist : rb_set name) (d : declaration) : feature_vec :=
name_set.of_list $ d.type.constants_set.to_list.filter $ λ n, ¬ blacklist.contains n
-- ignored_consts.foldl name_set.erase d.type.constants_set

meta def features_of_decl (n : name) : tactic feature_vec := do
bl ← mk_blacklist,
features_of_decl' bl <$> get_decl n

#eval features_of_decl ``add_comm >>= trace

@[inline]
meta def hist {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (l : list α) : rb_map α nat :=
l.foldl (λ hist a, hist.insert a ((hist.find a).get_or_else 0 + 1)) mk_rb_map

local attribute [inline] option.get_or_else
meta def df (docs : rb_map name feature_vec) : rb_map feature nat :=
hist $ docs.values >>= name_set.to_list

meta def doc_weight_prod (doc1 doc2 : feature_vec) (dfm : rb_map feature nat) : nat :=
list.sum $ doc1.to_list.map (λ f,
  if ¬ doc2.contains f then 0
  else dfm.size / (dfm.find f).get_or_else 0)

meta def doc_weight_dist (doc1 doc2 : feature_vec) (dfm : rb_map feature nat) (dfm_size := dfm.size) : nat :=
list.sum $
 doc1.to_list.map (λ f, if doc2.contains f then 0 else dfm_size / (dfm.find f).get_or_else 0) ++
 doc2.to_list.map (λ f, if doc1.contains f then 0 else dfm_size / (dfm.find f).get_or_else 0)

meta def doc_weight (doc : feature_vec) (dfm : rb_map feature nat) : nat :=
(doc.to_list.map (λ f, dfm.size / (dfm.find f).get_or_else 0)).sum

meta def select_for_goal (g : expr) : tactic (list $ name × nat) := do
e ← get_env,
bl ← mk_blacklist,
let lems := rb_map.of_list $
  e.get_trusted_decls.map (λ d, (d.to_name, features_of_decl' bl d)),
let dfm := df lems, let dfm_size := dfm.size,
let goal_fv := features_of_decl' bl (declaration.thm `_goal [] g (task.pure `(true.intro))),
let ws := lems.map (λ fv, doc_weight_dist goal_fv fv dfm dfm_size),
let ws := ws.to_list,
-- let ws := ws.filter (λ x, x.2 < 1000),
-- let ws := ws.to_list.filter (λ x : _ × _, x.2 ≠ 0),
let ws := ws.qsort (λ a b, a.2 < b.2),
-- trace $ ws.take 10,
trace $ ws.take 500,
pure ws

end hammer

namespace tactic

meta def reverted_target : tactic expr :=
retrieve $ do unfreeze_local_instances, revert_all, target >>= instantiate_mvars

namespace interactive

meta def feature_search (max := 10) : tactic unit := do
goal ← reverted_target,
lems ← hammer.select_for_goal goal,
(lems.take max).mmap' trace

end interactive
end tactic

set_option profiler true

example : ∀ x y : nat, x + y = y + x := by feature_search 20
