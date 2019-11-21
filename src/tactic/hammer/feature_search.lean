import data.list.defs meta.expr tactic.core

local attribute [inline] name.has_lt name.lt.decidable_rel bool.decidable_eq
decidable.to_bool cmp cmp_using native.mk_rb_map native.mk_rb_set native.rb_map.set_of_list
native.rb_map.of_list
-- set_option trace.compiler.optimize_bytecode true

meta def expr.constants_set (e : expr) : name_set :=
e.fold mk_name_set $ λ e _ s,
match e with
| (expr.const n _) := s.insert n
| _ := s
end

def list.zip_extend {α β} (a : α) : list α → list β → list (α × β)
| (a::as) (b::bs) := (a,b) :: list.zip_extend as bs
| [] (b::bs) := (a,b) :: list.zip_extend [] bs
| _ [] := []

@[inline]
meta def name.has_suffix (s : string) : name → bool
| (name.mk_string s' _) := s = s'
| _ := false

namespace hammer

open native tactic

meta def mk_ignore_args_for_type : expr → list bool
| (expr.pi _ binder_info.inst_implicit t e) := tt :: mk_ignore_args_for_type e
| (expr.pi _ _ bi e) := ff :: mk_ignore_args_for_type e
| _ := []

meta def mk_ignore_args : tactic (rb_map name (list bool)) := do
e ← get_env,
pure $ rb_map.of_list $ e.get_trusted_decls.map $ λ d,
  (d.to_name, mk_ignore_args_for_type d.type)

@[derive decidable_eq]
meta inductive feature
| c (n : name)
| digr (f a : name)

namespace feature

protected meta def to_string : feature → string
| (c n) := n.to_string
| (digr f a) := f.to_string ++ "→" ++ a.to_string

meta instance : has_to_string feature := ⟨feature.to_string⟩
meta instance : has_repr feature := ⟨feature.to_string⟩
meta instance : has_to_tactic_format feature := ⟨λ f, pure $ f.to_string⟩
meta instance : has_to_format feature := ⟨λ f, f.to_string⟩

@[inline]
protected meta def lt : feature → feature → bool
| (c n) (c n') := n < n'
| (digr f a) (digr f' a') := f < f' ∨ (f = f' ∧ a < a')
| (c _) (digr _ _) := true
| (digr _ _) (c _) := false

@[inline]
meta instance : has_lt feature := ⟨λ a b, feature.lt a b⟩

local attribute [inline] feature.lt

@[inline]
meta instance : decidable_rel ((<) : feature → feature → Prop) :=
by simp [(<)]; apply_instance

end feature

@[reducible]
meta def feature_vec :=
rb_set feature

private meta def ignored_consts : name_set :=
name_set.of_list [ ``Exists, ``and, ``or, ``iff, ``eq, ``heq, name.anonymous ]

private meta def sunfold_name := "_sunfold"
private meta def main_name := "_main"

meta def is_ignored_const (n : name) : bool :=
n.has_suffix sunfold_name ∨ n.has_suffix main_name ∨ ignored_consts.contains n

meta def head_sym_of (e : expr) : name :=
match e.get_app_fn with
| expr.const n _ := n
| _ := name.anonymous
end

meta def non_ignored_consts (il : rb_map name (list bool)) : expr → name_set → name_set
| (expr.pi _ binder_info.inst_implicit t e) := non_ignored_consts e
| (expr.lam _ binder_info.inst_implicit t e) := non_ignored_consts e
| (expr.pi _ _ t e) := non_ignored_consts t ∘ non_ignored_consts e
| (expr.lam _ _ t e) := non_ignored_consts t ∘ non_ignored_consts e
| (expr.var _) := id
| (expr.sort _) := id
| (expr.mvar _ _ _) := id
| (expr.local_const _ _ _ _) := id
| (expr.macro _ es) := λ fv, es.foldl (λ fv e, non_ignored_consts e fv) fv
| (expr.elet _ t v e) := non_ignored_consts t ∘ non_ignored_consts v ∘ non_ignored_consts e
| (expr.const n _) := if is_ignored_const n then id else λ cs, cs.insert n
| e@(expr.app _ _) := λ cs,
let fn := e.get_app_fn, as := e.get_app_args, hs := head_sym_of fn in
let cs := non_ignored_consts fn cs in
(((il.find hs).get_or_else []).zip_extend ff as).foldl
  (λ cs ⟨i, a⟩, if i then cs else non_ignored_consts a cs)
  cs

meta def features_of (il : rb_map name (list bool)) : expr → feature_vec → feature_vec
| (expr.pi _ binder_info.inst_implicit t e) := features_of e
| (expr.lam _ binder_info.inst_implicit t e) := features_of e
| (expr.pi _ _ t e) := features_of t ∘ features_of e
| (expr.lam _ _ t e) := features_of t ∘ features_of e
| (expr.var _) := id
| (expr.sort _) := id
| (expr.mvar _ _ _) := id
| (expr.local_const _ _ _ _) := id
| (expr.macro _ es) := λ fv, es.foldl (λ fv e, features_of e fv) fv
| (expr.elet _ t v e) := features_of t ∘ features_of v ∘ features_of e
| (expr.const n _) := if is_ignored_const n then id else λ fv, fv.insert (feature.c n)
| e@(expr.app _ _) := λ fv, let fn := e.get_app_fn, as := e.get_app_args, hs := head_sym_of fn in
  let fv := features_of fn fv in
  (((il.find hs).get_or_else []).zip_extend ff as).foldl
    (λ fv ⟨i, a⟩, if i then fv else
      let hsa := head_sym_of a,
          fv := if is_ignored_const hsa then fv else
            fv.insert (feature.digr hs hsa) in
      features_of a fv)
    fv

meta def mk_blacklist : tactic (rb_set name) := do
e ← get_env,
ds ← e.get_trusted_decls.mfilter (λ d, is_instance d.to_name),
cs ← attribute.get_instances `class,
pure $ rb_map.set_of_list $ ignored_consts.to_list ++ cs ++ ds.map (λ d, d.to_name)

meta def features_of_decl' (il : rb_map name (list bool)) (d : declaration) : feature_vec :=
features_of il d.type mk_rb_set
-- ignored_consts.foldl name_set.erase d.type.constants_set

meta def features_of_decl (n : name) : tactic feature_vec := do
il ← mk_ignore_args,
features_of_decl' il <$> get_decl n

#eval features_of_decl ``add_comm >>= trace

@[inline]
meta def hist {α} [has_lt α] [decidable_rel ((<) : α → α → Prop)] (l : list α) : rb_map α nat :=
l.foldl (λ hist a, hist.insert a ((hist.find a).get_or_else 0 + 1)) mk_rb_map

local attribute [inline] option.get_or_else
meta def df (docs : rb_map name feature_vec) : rb_map feature nat :=
hist $ docs.values >>= rb_set.to_list

meta def doc_weight_prod (doc1 doc2 : feature_vec) (dfm : rb_map feature nat) : nat :=
list.sum $ doc1.to_list.map (λ f,
  if ¬ doc2.contains f then 0
  else dfm.size / (dfm.find f).get_or_else 0)

meta def doc_weight_dist (doc1 doc2 : feature_vec) (dfm : rb_map feature nat) (dfm_size := dfm.size) : nat :=
list.sum $
 doc1.to_list.map (λ f, if doc2.contains f then 0 else dfm_size / (dfm.find f).get_or_else 0 / 10) ++
 doc2.to_list.map (λ f, if doc1.contains f then 0 else dfm_size / (dfm.find f).get_or_else 0)

meta def doc_weight (doc : feature_vec) (dfm : rb_map feature nat) : nat :=
(doc.to_list.map (λ f, dfm.size / (dfm.find f).get_or_else 0)).sum

meta def select_for_goal (g : expr) : tactic (list $ name × nat) := do
e ← get_env,
bl ← mk_ignore_args,
let lems := rb_map.of_list $
  list.filter (λ n, ¬ is_ignored_const n.1) $
  e.get_trusted_decls.map (λ d, (d.to_name, features_of_decl' bl d)),
let dfm := df lems, let dfm_size := dfm.size,
let goal_fv := features_of_decl' bl (declaration.thm `_goal [] g (task.pure `(true.intro))),
let ws := lems.map (λ fv, doc_weight_dist goal_fv fv dfm dfm_size),
let ws := ws.to_list,
-- let ws := ws.filter (λ x, x.2 < 1000),
-- let ws := ws.to_list.filter (λ x : _ × _, x.2 ≠ 0),
let ws := ws.qsort (λ a b, a.2 < b.2),
-- trace $ ws.take 10,
-- trace $ ws.take 500,
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

example : ∀ x y : nat, x + y = y + x := by feature_search 20; sorry
