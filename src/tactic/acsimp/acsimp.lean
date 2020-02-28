import tactic.acsimp.acmatch

open tactic expr native

namespace acsimp

/--
Computes the head symbol of a term.  E.g., ``head_sym `(1 + 2) = `has_add.add``.
-/
meta def head_sym (e : expr) : name := e.get_app_fn.const_name

/--
`acsimp_keys ty` computes the head symbols of all left-hand sides of the simp
lemma with type `ty`.
-/
meta def acsimp_keys : expr → set_builder name
| (pi n bi t lem) := acsimp_keys lem
| `(%%lhs = %%rhs) := {head_sym lhs}
| `(%%lhs ↔ %%rhs) := {head_sym lhs}
| `(%%a ∧ %%b) := acsimp_keys a ∪ acsimp_keys b
| `(¬ %%a) := {head_sym a}
| lem := {head_sym lem}

/--
Data structure containing the simplification lemmas for the AC simplifier.

The simp lemmas are stored as an `rb_lmap` where each simp lemma is indexed
by the head symbol of the left-hand side(s).
-/
meta def simp_lemmas :=
rb_lmap name expr

namespace simp_lemmas

meta instance : has_to_tactic_format simp_lemmas :=
show _root_.has_to_tactic_format (rb_map _ _), by apply_instance

/-- The empty simp set. -/
meta def empty : simp_lemmas := mk_rb_map

/--
`sls.add prf` adds a simplification lemma to the simp set.

The proof `prf` may contain metavariables. These will be assigned during
matching (inside a `tactic.retrieve`).
-/
meta def add (sls : simp_lemmas) (prf : expr) : tactic simp_lemmas := do
ty ← infer_type prf,
pure $ (acsimp_keys ty).to_list.foldr
  (λ k sls, sls.insert k prf)
  sls

/--
Calls `acsimp.simp_lemmas.add` to add each of the simp lemmas to the simp set.
-/
meta def add_list (sls : simp_lemmas) (prfs : list expr) : tactic simp_lemmas :=
prfs.mfoldl simp_lemmas.add sls

/--
`sls.add_const n` adds the simp lemma with name `n` to the simp set.
-/
meta def add_const (sls : simp_lemmas) (n : name) : tactic simp_lemmas := do
ns ← list.cons n <$> get_eqn_lemmas_for tt n,
ns.mfoldl (λ sls n, mk_const n >>= sls.add) sls

/--
`sls.add_simp n` adds the simp lemma with name `n` to the simp set.
-/
meta def add_simp := @add_const

/--
`sls.add_consts ns` adds each of the simp lemma with names in the list `ns`
to the simp set.
-/
meta def add_consts (sls : simp_lemmas) (ns : list name) : tactic simp_lemmas :=
ns.mfoldl simp_lemmas.add_const sls

private meta def simp_attr_lemma_names : tactic (list name) := do
env ← get_env,
env.fold (pure []) $ λ d ns, do
  ns ← ns,
  is_simp ← is_simp_lemma d.to_name,
  pure $ if is_simp then d.to_name :: ns else ns

/--
Constructs the default simp set consisting of all lemmas tagged with `@[simp]`.
-/
meta def mk_default (sls : simp_lemmas) : tactic simp_lemmas :=
simp_attr_lemma_names >>= sls.add_consts

/--
`sls.erase ns` removed the lemmas with names in `ns` from the simp set.
-/
meta def erase (sls : simp_lemmas) (ns : list name) : simp_lemmas :=
rb_map.map (list.filter $ λ e, e.get_app_fn.const_name ∉ ns) sls

/--
`sls.erase_const n` removed the lemma with name `n` from the simp set.
-/
meta def erase_const (sls : simp_lemmas) (n : name) : simp_lemmas :=
sls.erase [n]

end simp_lemmas

meta def or_refl (t : expr) : option expr → tactic expr
| none := mk_eq_refl t
| (some prf) := pure prf

section
variables (acsimp : expr → tactic (expr × option expr)) (sls : simp_lemmas)

/--
Given a term `op (op .. ..) (op .. ...)` applies `acsimp` at all the leaves.
Returns the simplified term, as well as a proof.
-/
meta def acsimp_ac_congr (op : expr) : expr → tactic (expr × option expr)
| lhs@(app (app op' a) b) := do
  is_eq ← option.is_some <$> (try_core $ is_def_eq op op'),
  if is_eq then do
    (a', prfa) ← acsimp_ac_congr a,
    (b', prfb) ← acsimp_ac_congr b,
    if prfa.is_none ∧ prfb.is_none then
      pure (op a b, none)
    else do
      prfa ← or_refl a prfa,
      prfb ← or_refl b prfb,
      prf ← mk_mapp ``congr_arg2 [none, op, none, none, none, none, prfa, prfb],
      pure (op a' b', prf)
  else
    acsimp lhs
| lhs := acsimp lhs

meta def with_goal {α} (m : expr) (t : tactic α) : tactic α := do
gs ← get_goals,
set_goals [m],
a ← t,
set_goals gs,
pure a

meta def solve_goal {α} (m : expr) (t : tactic α) : tactic α :=
with_goal m $ do a ← t, done, pure a

meta def acsimp_rwr_lem_core (t : expr) (ctxs : list expr) : expr → expr → tactic (expr × expr)
| lem_prf (pi n bi t lem) := do
  m ← mk_meta_var t,
  res ← acsimp_rwr_lem_core (lem_prf m) (lem.instantiate_var m),
  m ← instantiate_mvars m,
  when m.is_mvar (solve_goal m $ apply_instance <|> tactic.reflexivity),
  pure res
| eq_lhs_rhs `(%%lhs = %%rhs) :=
  first $ do ctx ← ctxs, pure $ do
  let lhs := ctx.subst lhs,
  let rhs := ctx.subst rhs,
  eq_lhs_rhs ← mk_congr_arg ctx eq_lhs_rhs,
  eq_lhs_t ← acmatch lhs t,
  eq_t_lhs ← mk_eq_symm eq_lhs_t,
  eq_t_rhs ← mk_eq_trans eq_t_lhs eq_lhs_rhs,
  pure (rhs, eq_t_rhs)
| eq_lhs_rhs `(%%lhs ↔ %%rhs) :=
  acsimp_rwr_lem_core (con ``propext [] lhs rhs eq_lhs_rhs)
    `(%%lhs = (%%rhs : Prop))
| prf `(%%a ∧ %%b) :=
  acsimp_rwr_lem_core (con ``and.left [] a b prf) a <|>
  acsimp_rwr_lem_core (con ``and.right [] a b prf) b
| prf `(¬ %%a) :=
  acsimp_rwr_lem_core (con ``eq_false_intro [] a prf) `(%%a = false)
| prf lem := do
  is_prop ← is_prop lem, guard is_prop,
  acsimp_rwr_lem_core (con ``eq_true_intro [] lem prf) `(%%lem = true)

meta def acsimp_rwr_lem (t : expr) (prf_lem : expr) (ctxs : list expr) : tactic (expr × expr) :=
retrieve $ do
lem ← infer_type prf_lem >>= instantiate_mvars,
(t', eq_t_t') ← acsimp_rwr_lem_core t ctxs prf_lem lem,
eq_t_t' ← instantiate_mvars eq_t_t',
t' ← instantiate_mvars t',
-- trace (con `rwr_lem [] prf_lem t t'),
pure (t', eq_t_t')

meta def acsimp_rwr (lhs : expr) : tactic (expr × option expr) :=
do t ← infer_type lhs,
let n := head_sym lhs,
let lems := sls.find n,
res ← (try_core $ first $ do l ← lems, pure $ acsimp_rwr_lem lhs l [lam `x binder_info.default t (var 0)]),
pure $ match res with some (rhs, prf) := (rhs, some prf) | none := (lhs, none) end

meta def acsimp_ac_rwr (op : expr) (lhs : expr) : tactic (expr × option expr) :=
do t ← infer_type lhs,
is_comm ← is_comm_op op,
let n := head_sym lhs,
let lems := sls.find n,
res ← (try_core $ first $ do l ← lems,
  pure $ do
    m ← mk_meta_var t,
    let ctxs := list.map (lam `x binder_info.default t) [var 0, op (var 0) m],
    acsimp_rwr_lem lhs l ctxs),
pure $ match res with some (rhs, prf) := (rhs, some prf) | none := (lhs, none) end

meta def acsimp_congr_core (t : expr) : expr → expr → tactic (expr × expr × bool)
| prf (pi n bi dom ty) := do
  m ← mk_meta_var dom,
  (t', eq_t_t', did_rw) ← acsimp_congr_core (prf m) (ty.instantiate_var m),
  m ← instantiate_mvars m,
  if m.is_mvar then do
    dom ← instantiate_mvars dom,
    match dom with
    | `(%%lhs = %%rhs) := do
      (rhs', prf) ← acsimp lhs,
      let did_rw_here : bool := prf.is_some,
      prf ← or_refl rhs' prf,
      unify rhs rhs',
      unify m prf,
      pure (t', eq_t_t', did_rw ∨ did_rw_here)
    | _ := trace (con `acsimp_congr_core_FAIL_CONGR [] dom) >> failure
    end
  else
    pure (t', eq_t_t', did_rw)
| prf `(%%lhs = %%rhs) := do
  unify lhs t,
  pure (rhs, prf, ff)
| _ ty := trace (con `acsimp_congr_core_FAIL [] ty) >> failure

meta def acsimp_congr (lhs : expr) : tactic (expr × option expr) := do
cl ← mk_specialized_congr_lemma_simp lhs,
retrieve $ do
(rhs, eq_lhs_rhs, did_rw) ← acsimp_congr_core acsimp lhs cl.proof cl.type,
if did_rw then do
  rhs ← instantiate_mvars rhs,
  eq_lhs_rhs ← instantiate_mvars eq_lhs_rhs,
  pure (rhs, eq_lhs_rhs)
else
  pure (lhs, none)

meta def acsimp_core_core (t : expr) : tactic (expr × option expr) := do
is_assoc ← try_core $ is_assoc_app t,
match is_assoc with
| some (op, is_assoc) := do
  -- trace (con `ac_congr [] op t),
  (t1, prf0) ← acsimp_ac_congr acsimp op t,
  (t2, prf1) ← acsimp_ac_rwr sls op t1,
  if prf0.is_none ∧ prf1.is_none then
    pure (t, none)
  else do
    (t3, prf2) ← if prf1.is_none then pure (t2, none) else acsimp t2,
    prf0 ← or_refl t1 prf0,
    prf1 ← or_refl t2 prf1,
    prf2 ← or_refl t3 prf2,
    prf ← mk_eq_trans prf0 prf1,
    prf ← mk_eq_trans prf prf2,
    pure (t3, prf)
| none := do
  (t1, prf0) ← acsimp_congr acsimp t,
  (t2, prf1) ← acsimp_rwr sls t1,
  if prf0.is_none ∧ prf1.is_none then
    pure (t, none)
  else do
    (t3, prf2) ← if prf1.is_none then pure (t2, none) else acsimp t2,
    prf0 ← or_refl t1 prf0,
    prf1 ← or_refl t2 prf1,
    prf2 ← or_refl t3 prf2,
    prf ← mk_eq_trans prf0 prf1,
    prf ← mk_eq_trans prf prf2,
    pure (t3, prf)
end

end

meta def acsimp_core (sls : simp_lemmas) : expr → tactic (expr × option expr) | t := do
(t', prf) ← acsimp_core_core acsimp_core sls t,
-- when prf.is_some $ trace (con `rwr [] t t'),
pure (t', prf)

end acsimp

namespace tactic
setup_tactic_parser

private meta def resolve_exception_ids (all_hyps : bool) : list name → list name → list name → tactic (list name × list name)
| []        gex hex := return (gex.reverse, hex.reverse)
| (id::ids) gex hex := do
  p ← resolve_name id,
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           := resolve_exception_ids ids (n::gex) hex
  | local_const n _ _ _ := when (not all_hyps) (fail $ sformat! "invalid local exception {id}, '*' was not used") >>
                           resolve_exception_ids ids gex (n::hex)
  | _                   := fail $ sformat! "invalid exception {id}, unknown identifier"
  end

private meta def add_simps : acsimp.simp_lemmas → list name → tactic acsimp.simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def report_invalid_simp_lemma {α : Type} (n : name): tactic α :=
fail format!"invalid simplification lemma '{n}' (use command 'set_option trace.simp_lemmas true' for more details)"

private meta def check_no_overload (p : pexpr) : tactic unit :=
when p.is_choice_macro $
  match p with
  | macro _ ps :=
    fail $ to_fmt "ambiguous overload, possible interpretations" ++
           format.join (ps.map (λ p, (to_fmt p).indent 4))
  | _ := failed
  end

private meta def simp_lemmas.resolve_and_add (s : acsimp.simp_lemmas) (u : list name) (n : name) (ref : pexpr) : tactic (acsimp.simp_lemmas × list name) :=
do
  p ← resolve_name n,
  check_no_overload p,
  -- unpack local refs
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           :=
    (do b ← is_valid_simp_lemma_cnst n, guard b, save_const_type_info n ref, s ← s.add_simp n, return (s, u))
    <|>
    (do eqns ← get_eqn_lemmas_for tt n, guard (eqns.length > 0), save_const_type_info n ref, s ← add_simps s eqns, return (s, u))
    <|>
    (do env ← get_env, guard (env.is_projection n).is_some, return (s, n::u))
    <|>
    report_invalid_simp_lemma n
  | _ :=
    (do e ← i_to_expr_no_subgoals p, b ← is_valid_simp_lemma e, guard b, try (save_type_info e ref), s ← s.add e, return (s, u))
    <|>
    report_invalid_simp_lemma n
  end

private meta def simp_lemmas.add_pexpr (s : acsimp.simp_lemmas) (u : list name) (p : pexpr) : tactic (acsimp.simp_lemmas × list name) :=
match p with
| (const c [])          := simp_lemmas.resolve_and_add s u c p
| (local_const c _ _ _) := simp_lemmas.resolve_and_add s u c p
| _                     := do new_e ← i_to_expr_no_subgoals p, s ← s.add new_e, return (s, u)
end

private meta def simp_lemmas.append_pexprs : acsimp.simp_lemmas → list name → list pexpr → tactic (acsimp.simp_lemmas × list name)
| s u []      := return (s, u)
| s u (l::ls) := do (s, u) ← simp_lemmas.add_pexpr s u l, simp_lemmas.append_pexprs s u ls

@[nolint unused_arguments]
meta def join_user_acsimp_lemmas (no_dflt : bool) (attrs : list name) : tactic acsimp.simp_lemmas := do
sls ← if no_dflt then pure acsimp.simp_lemmas.empty
      else acsimp.simp_lemmas.mk_default acsimp.simp_lemmas.empty,
-- TODO
pure sls

meta def mk_acsimp_set_core (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) (at_star : bool)
                          : tactic (bool × acsimp.simp_lemmas × list name) :=
do (hs, gex, hex, all_hyps) ← decode_simp_arg_list hs,
   when (all_hyps ∧ at_star ∧ not hex.empty) $ fail "A tactic of the form `simp [*, -h] at *` is currently not supported",
   s      ← join_user_acsimp_lemmas no_dflt attr_names,
   (s, u) ← simp_lemmas.append_pexprs s [] hs,
   s      ← if not at_star ∧ all_hyps then do
              ctx ← collect_ctx_simps,
              let ctx := ctx.filter (λ h, h.local_uniq_name ∉ hex), -- remove local exceptions
              s.add_list ctx
            else return s,
   -- add equational lemmas, if any
   gex ← gex.mmap (λ n, list.cons n <$> get_eqn_lemmas_for tt n),
   return (all_hyps, acsimp.simp_lemmas.erase s $ gex.join, u)

meta def mk_acsimp_set (no_dflt : bool) (attr_names : list name) (hs : list simp_arg_type) : tactic (acsimp.simp_lemmas × list name) :=
prod.snd <$> (mk_acsimp_set_core no_dflt attr_names hs ff)

namespace interactive
open interactive interactive.types expr

@[nolint unused_arguments]
meta def acsimp_target (s : acsimp.simp_lemmas) (to_unfold : list name := []) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic bool := do
t ← target >>= instantiate_mvars,
(new_t, pr) ← acsimp.acsimp_core s t,
match pr with
| none := pure ff
| some pr := do
  replace_target new_t pr,
  pure tt
end

meta def acsimp_core_aux (cfg : simp_config) (discharger : tactic unit) (s : acsimp.simp_lemmas) (u : list name) (hs : list expr) (tgt : bool) : tactic unit :=
do to_remove ← hs.mfilter $ λ h, do {
         h_type ← infer_type h,
         (do (new_h_type, pr) ← acsimp.acsimp_core s h_type, --simplify s u h_type cfg `eq discharger,
             pr ← acsimp.or_refl new_h_type pr,
             assert h.local_pp_name new_h_type,
             mk_eq_mp pr h >>= tactic.exact >> return tt)
         <|>
         (return ff) },
   goal_simplified ←
    if tgt then acsimp_target s u cfg discharger else return ff,
   guard (cfg.fail_if_unchanged = ff ∨ to_remove.length > 0 ∨ goal_simplified) <|> fail "simplify tactic failed to simplify",
   to_remove.mmap' (λ h, try (tactic.clear h))

meta structure acsimp_all_entry :=
(h        : expr) -- hypothesis
(new_type : expr) -- new type
(pr       : option expr) -- proof that type of h is equal to new_type
(s        : acsimp.simp_lemmas) -- simplification lemmas for simplifying new_type

private meta def update_simp_lemmas (es : list acsimp_all_entry) (h : expr) : tactic (list acsimp_all_entry) :=
es.mmap $ λ e, do new_s ← e.s.add h, return {s := new_s, ..e}

/- Helper tactic for `init`.
   Remark: the following tactic is quadratic on the length of list expr (the list of non dependent propositions).
   We can make it more efficient as soon as we have an efficient simp_lemmas.erase. -/
private meta def init_aux : list expr → acsimp.simp_lemmas → list acsimp_all_entry → tactic (acsimp.simp_lemmas × list acsimp_all_entry)
| []      s r := return (s, r)
| (h::hs) s r := do
  new_r  ← update_simp_lemmas r h,
  new_s  ← s.add h,
  h_type ← infer_type h,
  init_aux hs new_s (⟨h, h_type, none, s⟩::new_r)

private meta def init (s : acsimp.simp_lemmas) (hs : list expr) : tactic (acsimp.simp_lemmas × list acsimp_all_entry) :=
init_aux hs s []

private meta def add_new_hyps (es : list acsimp_all_entry) : tactic unit :=
es.mmap' $ λ e,
   match e.pr with
   | none    := return ()
   | some pr :=
      assert e.h.local_pp_name e.new_type >>
      mk_eq_mp pr e.h >>= tactic.exact
   end

private meta def clear_old_hyps (es : list acsimp_all_entry) : tactic unit :=
es.mmap' $ λ e, when (e.pr ≠ none) (try (tactic.clear e.h))

private meta def join_pr : option expr → expr → tactic expr
| none       pr₂ := return pr₂
| (some pr₁) pr₂ := mk_eq_trans pr₁ pr₂

private meta def loop (cfg : simp_config) (discharger : tactic unit) (to_unfold : list name)
                      : list acsimp_all_entry → list acsimp_all_entry → acsimp.simp_lemmas → bool → tactic unit
| []      r  s m :=
  if m then loop r [] s ff
  else do
    add_new_hyps r,
    target_changed ← acsimp_target s to_unfold cfg discharger,
    guard (cfg.fail_if_unchanged = ff ∨ target_changed ∨ r.any (λ e, e.pr ≠ none)) <|> fail "simp_all tactic failed to simplify",
    clear_old_hyps r
| (e::es) r  s m := do
   let ⟨h, h_type, h_pr, s'⟩ := e,
   (new_h_type, new_pr) ← acsimp.acsimp_core s' h_type, --- simplify s' to_unfold h_type {fail_if_unchanged := ff, ..cfg} `eq discharger,
   new_pr ← acsimp.or_refl new_h_type new_pr,
   if h_type =ₐ new_h_type then loop es (e::r) s m
   else do
     new_pr      ← join_pr h_pr new_pr,
     new_fact_pr ← mk_eq_mp new_pr h,
     if new_h_type = `(false) then do
       tgt         ← target,
       to_expr ``(@false.rec %%tgt %%new_fact_pr) >>= tactic.exact
     else do
       h0_type     ← infer_type h,
       let new_fact_pr := mk_id_proof new_h_type new_fact_pr,
       new_es      ← update_simp_lemmas es new_fact_pr,
       new_r       ← update_simp_lemmas r new_fact_pr,
       let new_r := {new_type := new_h_type, pr := new_pr, ..e} :: new_r,
       new_s       ← s.add new_fact_pr,
       loop new_es new_r new_s tt

private meta def acsimp_all (s : acsimp.simp_lemmas) (to_unfold : list name) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic unit :=
do hs      ← non_dep_prop_hyps,
   (s, es) ← init s hs,
   loop cfg discharger to_unfold es [] s ff

meta def acsimp_core (cfg : simp_config) (discharger : tactic unit)
                   (no_dflt : bool) (hs : list simp_arg_type) (attr_names : list name)
                   (locat : loc) : tactic unit :=
match locat with
| loc.wildcard := do (all_hyps, s, u) ← mk_acsimp_set_core no_dflt attr_names hs tt,
                     if all_hyps then acsimp_all s u cfg discharger
                     else do hyps ← non_dep_prop_hyps, acsimp_core_aux cfg discharger s u hyps tt
| _            := do (s, u) ← mk_acsimp_set no_dflt attr_names hs,
                     ns ← locat.get_locals,
                     acsimp_core_aux cfg discharger s u ns locat.include_goal
end
>> try tactic.triv >> try (tactic.reflexivity reducible)

/--
The `acsimp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.

`acsimp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

`acsimp [h₁ h₂ ... hₙ]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions. If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.

`acsimp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.

`acsimp *` is a shorthand for `simp [*]`.

`acsimp only [h₁ h₂ ... hₙ]` is like `simp [h₁ h₂ ... hₙ]` but does not use `[simp]` lemmas

`acsimp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `idᵢ`.

`acsimp at h₁ h₂ ... hₙ` simplifies the non-dependent hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. The tactic fails if the target or another hypothesis depends on one of them. The token `⊢` or `|-` can be added to the list to include the target.

`acsimp at *` simplifies all the hypotheses and the target.

`acsimp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

`acsimp with attr₁ ... attrₙ` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr₁]`, ..., `[attrₙ]` or `[simp]`.
-/
meta def acsimp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
propagate_tags (acsimp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)

/--
Just construct the simp set and trace it. Used for debugging.
-/
meta def trace_acsimp_set (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list) : tactic unit :=
do (s, _) ← mk_acsimp_set no_dflt attr_names hs,
   trace s

end interactive

end tactic
