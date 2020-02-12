import tactic.hammer.feature_search system.io tactic.core meta.coinductive_predicates
tactic.hammer.fol
tactic.hammer.fo_translation
super

open tactic expr native

namespace hammer

namespace fotr2

@[derive [has_to_string, has_repr, has_to_tactic_format, has_to_format, decidable_eq]]
inductive arg_mode
| dropped
| param
| appl

meta def occurs_in_dropped : expr → list arg_mode → bool
| (expr.pi _ _ ty body) (m :: ms) :=
  (ty.has_var ∧ m = arg_mode.dropped) ∨
    occurs_in_dropped (body.instantiate_var `(Prop)) ms
| _ _ := ff

meta def occurs_in_non_dropped : expr → list arg_mode → bool
| (expr.pi _ _ ty body) (m :: ms) :=
  (ty.has_var ∧ m ≠ arg_mode.dropped) ∨
    occurs_in_non_dropped (body.instantiate_var `(Prop)) ms ∨
    occurs_in_non_dropped (body.instantiate_vars [var 0, `(Prop)]) ms
| _ _ := ff

meta def is_coherent_tc : expr → tactic bool :=
is_class

meta structure compute_arg_modes_cfg :=
(drop_inst_args := tt)
(drop_dep_args := tt)
(param_all_args := ff)
(param_all_cls_args := tt)

meta def compute_arg_modes_core (cfg : compute_arg_modes_cfg) : expr → tactic (list arg_mode)
| (expr.pi bn bi ty body) := do
  l ← mk_local' bn bi ty,
  modes ← compute_arg_modes_core (body.instantiate_var l),
  irrelevant ← succeeds (mk_mapp ``subsingleton [ty] >>= mk_instance),
  is_tc ← is_coherent_tc ty,
  if irrelevant ∨ (cfg.drop_inst_args ∧ is_tc) then
    pure $ arg_mode.dropped :: modes
  else if cfg.drop_dep_args ∧ occurs_in_non_dropped body modes then
    pure $ arg_mode.dropped :: modes
  else if occurs_in_dropped body modes then
    pure $ arg_mode.param :: modes
  else if cfg.param_all_args then
    pure $ arg_mode.param :: modes
  else
    pure $ if modes = [] then [] else arg_mode.appl :: modes
| _ := pure []

meta def compute_arg_modes (cfg : compute_arg_modes_cfg) (n : name) (t : expr) :
  tactic (list arg_mode) := do
is_cls ← has_attribute' `class n,
let cfg := if is_cls ∧ cfg.param_all_cls_args then {param_all_args := tt, ..cfg} else cfg,
compute_arg_modes_core cfg t

-- #print list.sum
-- #eval let n := `list.sum in mk_const n >>= infer_type >>= compute_arg_modes {} n >>= trace

@[derive [has_to_string, has_repr, has_to_tactic_format, has_to_format]]
meta structure trans_out :=
(n : name)
(fml : fo_fml)
(prf : expr)

@[derive [has_to_string, has_repr, has_to_tactic_format, has_to_format]]
meta structure trans_state :=
(fresh_idx : ℕ := 0)
(modes : name_map (list arg_mode) := mk_name_map)
(var_names : name_map name := mk_name_map)
(abbrs : rb_map expr expr := mk_rb_map)
(out : list trans_out := [])

@[reducible]
meta def trans := state_t trans_state tactic

meta def trans.decl_out (n : name) (prf : expr) (f : fo_fml) : trans unit :=
state_t.modify $ λ s, { out := ⟨n, f, prf⟩ :: s.out, ..s }

meta def get_arg_modes_for_head (e : expr) (cfg : compute_arg_modes_cfg := {}) :
  trans (list arg_mode) := do
let h := e.get_app_fn,
let n := match h with
         | e@(expr.local_const n _ _ _) := n
         | c@(expr.const n _) := n
         | _ := `_
         end,
if n = `_ then pure [] else do
s ← state_t.get,
match s.modes.find n with
| some ms := pure ms
| _ := do
  t ← match h with
      | e@(expr.local_const _ _ _ _) := state_t.lift $ infer_type e
      | c@(expr.const n _) := state_t.lift $ declaration.type <$> get_decl n
      | _ := pure $ mk_sorry `(Prop)
      end,
  ms ← state_t.lift $ compute_arg_modes cfg n t,
  state_t.put { modes := s.modes.insert n ms, ..s },
  pure ms
end

meta def fresh_num : trans ℕ := do
state_t.modify (λ s, { fresh_idx := s.fresh_idx + 1, ..s }),
trans_state.fresh_idx <$> state_t.get

meta def fresh_name (hint : name) : trans name :=
do n ← fresh_num, pure $ name.mk_numeral (unsigned.of_nat n) hint

meta def get_var_name (e : expr) : trans name := do
n ← (λ s : trans_state, s.var_names.find e.local_uniq_name) <$> state_t.get,
match n with
| some n := pure n
| none := do
  n ← fresh_name e.local_pp_name,
  state_t.modify $ λ s, { var_names := s.var_names.insert e.local_uniq_name n, ..s },
  pure n
end

meta def abbr (e : expr) (n : name) : trans (expr × bool) := do
e' ← (λ s : trans_state, s.abbrs.find e) <$> state_t.get,
match e' with
| some e' := pure (e', ff)
| none := do
  t ← state_t.lift $ infer_type e,
  e' ← state_t.lift $ mk_local_def n t,
  state_t.modify $ λ s, { abbrs := s.abbrs.insert e e', ..s },
  pure (e', tt)
end

meta def apply_modes {α} : list arg_mode → list α → list α × list α
| [] as := ([], as)
| (arg_mode.dropped::ms) (a::as) := apply_modes ms as
| (arg_mode.appl::ms) (a::as) :=
  let (ps, bs) := apply_modes ms as in
  (ps, a :: bs)
| (arg_mode.param::ms) (a::as) :=
  let (ps, bs) := apply_modes ms as in
  (a :: ps, bs)
| _ [] := ([], [])

meta def fo_app (a b : fo_term) := fo_term.fn `_A [a, b]

meta def is_effective_prop (e : expr) : trans bool :=
state_t.lift $ bor <$> is_prop e <*> is_coherent_tc e

meta def eta_expand : expr → ℕ → tactic expr
| e 0 := pure e
| e (n+1) := do
  t ← infer_type e >>= whnf,
  match t with
  | (pi bn bi dom cod) := do
    l ← mk_local' bn bi dom,
    mk_lambda l <$> eta_expand (e l) n
  | _ := do t ← pp t, fail $ to_fmt "cannot eta-expand " ++ t
  end

meta def extract_from_lctx : list expr → expr → expr × list expr
| [] e := (e, [])
| (x::lctx) e :=
  let e := e.abstract_local x.local_uniq_name in
  if e.has_var then
    let (e, lctx) := extract_from_lctx lctx $
      lam x.local_pp_name x.local_binding_info x.local_type e in
    (e, x::lctx)
  else
    extract_from_lctx lctx e

meta mutual def trans_term, trans_type, trans_fml, trans_decl
with trans_term : list expr → expr → trans fo_term | lctx t := do
t ← state_t.lift $ zeta t,
t ← state_t.lift $ head_beta t,
is_proof ← state_t.lift (is_proof t),
if is_proof then pure term_prf else do
let hd := t.get_app_fn,
let as := t.get_app_args,
match hd with
| `(auto_param %%hd _) := trans_term lctx (hd.mk_app as)
| (const n _) := do
  ms ← get_arg_modes_for_head hd,
  if ms.length > as.length then -- eta-expand
    state_t.lift (eta_expand t (ms.length - as.length)) >>= trans_term lctx
  else do
    let (ps, as) := apply_modes ms as,
    ps ← ps.mmap (trans_term lctx),
    as ← as.mmap (trans_term lctx),
    pure $ list.foldl fo_app (fo_term.fn n ps) as
| (local_const _ pretty bi ty) := do
  vn ← get_var_name hd,
  if hd ∈ lctx then do
    list.foldl fo_app (fo_term.var vn) <$> as.mmap (trans_term lctx)
  else do
    ms ← get_arg_modes_for_head hd,
    if ms.length > as.length then -- eta-expand
      state_t.lift (eta_expand t (ms.length - as.length)) >>= trans_term lctx
    else do
      let (ps, as) := apply_modes ms as,
      ps ← ps.mmap (trans_term lctx),
      as ← as.mmap (trans_term lctx),
      pure $ list.foldl fo_app (fo_term.fn vn ps) as
  | (app _ _) := state_t.lift $ fail "trans_term head is app"
  | (sort _) := pure $ fo_term.const `_S
  | (elet pp_n t v b) := trans_term lctx (b.instantiate_var t)
  | (mvar n _ _) := pure $ fo_term.const n
  | (macro _ es) := do
    hd' ← match is_sorry hd with
    | some t := do
      t' ← trans_term lctx t,
      pure $ fo_term.fn `_sorry [t']
    | none := do
    e ← state_t.lift get_env,
    let hd := (_root_.try_for 1000 (e.unfold_all_macros hd)).get_or_else hd,
    match hd with
    | (macro _ _) := do
      let (f, as) := extract_from_lctx lctx hd,
      (f', is_new) ← abbr f `_macro,
      when is_new (do
        f_ty ← state_t.lift $ infer_type f,
        n ← get_var_name f',
        trans_decl n f f_ty),
      trans_term lctx (f'.mk_app as.reverse)
    | _ := trans_term lctx hd
    end
    end,
    list.foldl fo_app hd' <$> as.mmap (trans_term lctx)
  | (var _) := state_t.lift (fail "open term")
  | (lam _ _ _ _) := do
    let (f, capts) := extract_from_lctx lctx hd,
    (f', is_new) ← abbr f `_lambda,
    get_arg_modes_for_head f' {param_all_args := ff},
    when is_new (do
      f_ty ← state_t.lift $ infer_type f,
      n ← get_var_name f',
      trans_decl n f f_ty,
      trans_decl (n.mk_string "eqn") f $ `(@eq.{1} %%f_ty %%f' %%f)),
    trans_term lctx (f'.mk_app (capts.reverse++as))
  | (pi _ _ _ _) := do
    let (f, capts) := extract_from_lctx lctx hd,
    (f', is_new) ← abbr f `_pi,
    when is_new (do
      f_ty ← state_t.lift $ infer_type f,
      n ← get_var_name f',
      trans_decl n f f_ty,
      when false $ do -- vampire really doesn't like this...
        x ← state_t.lift $ mk_local_def `x hd,
        eqn ← fo_fml.iff
          <$> trans_type (x::capts) x (f'.mk_app capts.reverse)
          <*> trans_type (x::capts) x hd,
        eqn ← capts.mfoldl (λ eqn a, do a' ← get_var_name a, pure $ fo_fml.all a' eqn) eqn,
        x' ← get_var_name x,
        trans.decl_out (n.mk_string "eqn") f (fo_fml.all x' eqn)),
    trans_term lctx (f'.mk_app (capts.reverse++as))
end
with trans_type : list expr → expr → expr → trans fo_fml | lctx e t := do
t_is_prop ← state_t.lift $ is_prop t,
t_is_tc ← state_t.lift $ is_coherent_tc t,
if t_is_tc then do
  trans_fml lctx t
else if t_is_prop then do
  e' ← trans_term lctx e,
  fo_fml.and (fo_fml.eq e' term_prf) <$> trans_fml lctx t
else match t with
-- | (sort level.zero) :=
--   pure $ fo_fml.or (fo_fml.eq _ _) (fo_fml.eq _ _)
| `(auto_param %%t _) := trans_type lctx e t
| (sort l) := pure fo_fml.true
| (pi pp_n bi a b) := do
  a_is_prop ← is_effective_prop a,
  x ← state_t.lift $ mk_local' pp_n bi a,
  x' ← get_var_name x,
  b' ← trans_type (x::lctx) (e.app x) (b.instantiate_var x),
  if a_is_prop then do
    a' ← trans_fml lctx a,
    pure $ fo_fml.imp a' b'
  else do
    a' ← trans_type (x::lctx) x a,
    pure $ fo_fml.all x' $ fo_fml.imp a' b'
| _ := do
  e' ← trans_term lctx e,
  t' ← trans_term lctx t,
  pure (fo_fml.pred `_T [e', t'])
end
with trans_fml : list expr → expr → trans fo_fml | lctx t :=
match t with
| `(auto_param %%t _) := trans_fml lctx t
| `(@eq %%t %%(a@(expr.lam pp_n bi c _)) %%b) := do
  x ← state_t.lift $ mk_local' pp_n bi c,
  x' ← get_var_name x,
  a' ← state_t.lift $ tactic.head_beta $ app a x,
  b' ← state_t.lift $ tactic.head_beta $ app b x,
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x' <$>
    (fo_fml.imp <$> trans_type (x::lctx) x c <*>
      trans_fml (x::lctx) `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%(b@(expr.lam pp_n bi c _))) := do
  x ← state_t.lift $ mk_local' pp_n bi c,
  x' ← get_var_name x,
  a' ← state_t.lift $ tactic.head_beta $ app a x,
  b' ← state_t.lift $ tactic.head_beta $ app b x,
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x' <$>
    (fo_fml.imp <$> trans_type (x::lctx) x c <*>
      trans_fml (x::lctx) `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%b) := do
  a_is_prop ← state_t.lift $ is_prop a,
  if a_is_prop then
    trans_fml lctx `(%%a ↔ %%b)
  else
    fo_fml.eq <$> trans_term lctx a <*> trans_term lctx b
| `(@heq %%t %%t' %%a %%b) :=
  fo_fml.and <$> (fo_fml.eq <$> trans_term lctx t <*> trans_term lctx t')
    <*> (fo_fml.eq <$> trans_term lctx a <*> trans_term lctx b)
| `(¬ %%a) := fo_fml.neg <$> trans_fml lctx a
| `(@ne %%t %%a %%b) := trans_fml lctx `(¬ (@eq.{1} %%t %%a %%b))
| `(%%a ∧ %%b) := fo_fml.and <$> trans_fml lctx a <*> trans_fml lctx b
| `(%%a ∨ %%b) := fo_fml.or <$> trans_fml lctx a <*> trans_fml lctx b
| `(%%a ↔ %%b) := fo_fml.iff <$> trans_fml lctx a <*> trans_fml lctx b
| `(decidable_pred _) := pure fo_fml.true
| `(decidable_rel _) := pure fo_fml.true
| `(decidable_eq _) := pure fo_fml.true
| `(decidable _) := pure fo_fml.true
| `(nonempty %%t) := do
  t_is_prop ← is_effective_prop t,
  if t_is_prop then
    trans_fml lctx t
  else do
    x ← state_t.lift $ mk_local_def `x t,
    x' ← get_var_name x,
    fo_fml.ex x' <$> trans_type (x::lctx) x t
| `(inhabited %%t) := trans_fml lctx `(nonempty.{1} %%t)
| `(Exists %%(expr.lam pp_n bi a b)) :=
  if b.has_var_idx 0 then do
    x ← state_t.lift $ mk_local' pp_n bi a,
    x' ← get_var_name x,
    a' ← trans_type (x::lctx) x a,
    b' ← trans_fml (x::lctx) (b.instantiate_var x),
    pure (fo_fml.ex x' $ fo_fml.and a' b')
  else
    fo_fml.and <$> trans_fml lctx a <*> trans_fml lctx b
| (pi pp_n bi a b) := do
  a_prop ← is_effective_prop a,
  if b.has_var_idx 0 ∧ ¬ a_prop then do
    x ← state_t.lift $ mk_local' pp_n bi a,
    x' ← get_var_name x,
    a' ← trans_type (x::lctx) x a,
    b' ← trans_fml (x::lctx) (b.instantiate_var x),
    pure (fo_fml.all x' $ fo_fml.imp a' b')
  else
    fo_fml.imp <$> trans_fml lctx a <*> trans_fml lctx (b.instantiate_var (mk_sorry a))
| _ := do t' ← trans_term lctx t, pure (fo_fml.pred `_P [t'])
end
with trans_decl : name → expr → expr → trans unit | n e t := do
env ← state_t.lift get_env,
let e := (_root_.try_for 1000 (env.unfold_all_macros e)).get_or_else e,
let t := (_root_.try_for 1000 (env.unfold_all_macros t)).get_or_else t,
t_is_prop ← is_effective_prop t,
t' ←
  if t_is_prop then
    trans_fml [] t
  else
    trans_type [] e t,
trans.decl_out n e t'

meta def trans_decl' (d : declaration) : trans unit :=
trans_decl d.to_name (const d.to_name (d.univ_params.map level.param)) d.type

-- #eval do
-- d ← get_decl `coe,
-- ((), out) ← (trans_decl' d).run {},
-- out.out.mmap $ λ out,
-- trace $ tptpify_ann "axiom" out.n out.fml

meta def is_good_const : name → Prop
| ``Exists := ff
| _ := tt

meta instance : decidable_pred is_good_const :=
by delta is_good_const; apply_instance

meta def close_under_references_core : list name → rb_set name → tactic (rb_set name)
| [] s := pure s
| (n::ns) s :=
  if s.contains n then
    close_under_references_core ns s
  else do
    ff ← is_instance n | close_under_references_core ns s,
    cs ← (do d ← get_decl n, pure $ some $ d.type.constants.filter is_good_const) <|> pure none,
    match cs with
    | none := close_under_references_core ns s
    | some cs := close_under_references_core (cs ++ ns) (s.insert n)
    end

meta def close_under_references (ns : list name) : tactic (list name) :=
rb_set.to_list <$> close_under_references_core ns mk_rb_set

meta def explicit_arg_heads_core : list expr → expr → list name
| (a::as) (pi _ bi _ t) :=
  let rest := explicit_arg_heads_core as t in
  if bi ≠ binder_info.default then rest else
  match a.get_app_fn with
  | (const n _) := n :: rest
  | _ := rest
  end
| _ _ := []

meta def get_explicit_arg_heads (e : expr) : tactic (list name) :=
match e.get_app_fn with
| (const n _) := do
  t ← declaration.type <$> get_decl n,
  pure $ n :: explicit_arg_heads_core e.get_app_args t
| _ := pure []
end

meta def inst_implicit_dom_heads : expr → list name
| (pi _ binder_info.inst_implicit d c) :=
  match d.get_app_fn with
  | const n _ := n :: inst_implicit_dom_heads c
  | _ := inst_implicit_dom_heads c
  end
| (pi _ _ _ c) := inst_implicit_dom_heads c
| _ := []

meta def close_under_instances_core (all_cs : name_map (list name)) :
  list name → name_set → name_set → tactic name_set
| [] done cnsts := pure cnsts
| (c::cs) done cnsts :=
  if done.contains c then
    close_under_instances_core cs done cnsts
  else do
    let done := done.insert c,
    ct ← declaration.type <$> get_decl c,
    new_is ← list.join <$> ((all_cs.find c).get_or_else []).mmap (λ i, do
      v ← declaration.type <$> get_decl i,
      let cod_hs := explicit_arg_heads_core v.pi_codomain.get_app_args ct,
      pure $ if ¬ ∀ n ∈ cod_hs, cnsts.contains n then
        []
      else
        [i]),
    new_cs ← list.join <$> new_is.mmap (λ i,
      (inst_implicit_dom_heads ∘ declaration.type) <$> get_decl i),
    let cs := new_cs.filter (λ c, ¬ done.contains c) ++ cs,
    let cnsts := new_is.foldl name_set.insert cnsts,
    close_under_instances_core cs done cnsts

meta def close_under_instances (ns : list name) : tactic (list name) := do
is ← attribute.get_instances `instance,
is ← is.mmap get_decl,
let is := is.filter (λ i, i.is_trusted),
let cs := rb_lmap.of_list $ is.map $ λ i,
  (i.type.pi_codomain.get_app_fn.const_name, i.to_name),
name_set.to_list <$>
  close_under_instances_core cs (ns.filter (λ n, cs.contains n)) mk_name_set (name_set.of_list ns)

meta def close_under_equations (ns : list name) : tactic (list name) :=
(list.dup_by_native id ∘ (++ ns) ∘ list.join) <$>
  ns.mmap (λ n, do
    is_tc ← has_attribute' `instance n,
    if is_tc then pure [] else
      get_eqn_lemmas_for tt n <|> pure [])

meta def bad_lemmas : name_set :=
name_set.of_list []

meta def do_trans (axs : list name) : tactic (format × list (string × expr × name)) :=
(λ t : trans _, prod.fst <$> t.run {}) $ do
rgoal ← state_t.lift reverted_target,
let axs := rgoal.constants.filter is_good_const ++ axs,
axs ← state_t.lift $ close_under_references axs,
axs ← state_t.lift $ close_under_equations axs,
axs ← state_t.lift $ close_under_instances axs,
env ← state_t.lift get_env,
cs ← state_t.lift $ name_set.of_list <$> attribute.get_instances `class,
let axs := axs.filter (λ ax, ¬ (env.is_constructor ax ∧ cs.contains ax.get_prefix)),
let axs := axs.filter (λ ax, ¬ bad_lemmas.contains ax),
let axs := axs.qsort (λ a b : name, (a.lex_cmp b) = ordering.lt),
axs.mmap' (λ n, do
  d ← state_t.lift $ get_decl n,
  trans_decl' d
  -- mwhen (state_t.lift $ is_instance n) (do
  --   eqns ← state_t.lift $ super.mk_inst_equations n,
  --   eqns.mmap' $ λ eqn, do
  --     ty ← state_t.lift $ infer_type eqn,
  --     trans_decl n eqn ty)
      ),
lctx ← state_t.lift tactic.local_context,
lctx.mmap' (λ l, do
  n ← get_var_name l,
  t ← state_t.lift $ infer_type l,
  trans_decl n l t),
out ← trans_state.out <$> state_t.get,
let anns := (do
  o ← out,
  guard (¬ o.fml.is_trivially_true),
  [tptpify_ann "axiom" o.n o.fml.simp]),
goal ← state_t.lift target,
goal_is_prop ← state_t.lift $ tactic.is_prop goal,
goal' ← if goal_is_prop then trans_fml [] goal
  else (do
    x ← state_t.lift $ mk_local_def `goal goal,
    x' ← get_var_name x,
    fo_fml.ex x' <$> trans_type [x] x goal),
let anns := (tptpify_ann "conjecture" `_goal goal'.simp) :: anns,
let tptp := format.join $ list.intersperse (format.line ++ format.line) anns.reverse,
pure (tptp, out.map (λ o, (ax_tptpify_name o.n, o.prf, o.n)))

meta def exec_cmd (cmd : string) (args : list string) (stdin : string) : tactic string :=
tactic.unsafe_run_io $ do
child ← io.proc.spawn {
  cmd := cmd, args := args,
  stdin := io.process.stdio.piped,
  stdout := io.process.stdio.piped,
},
io.fs.write child.stdin stdin.to_char_buffer,
io.fs.close child.stdin,
buf ← io.fs.read_to_end child.stdout,
io.fs.close child.stdout,
exitv ← io.proc.wait child,
when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
return buf.to_string

meta def run_vampire (tptp : string) : tactic string :=
timetac "vampire took" $
exec_cmd "vampire" ["-p", "tptp"] tptp

meta def filter_lemmas (axs : list name) : tactic (list (expr × name)) := do
(tptp, ax_names) ← do_trans axs,
(tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
let ax_names := rb_map.of_list ax_names,
tptp_out ← timetac "vampire took" $ exec_cmd "bash" ["-c",
  "vampire -p tptp -t 30s --output_axiom_names on | " ++
    "grep -oP '(?<=file\\(unknown,).*?(?=\\))'"]
  tptp.to_string,
let ns := tptp_out.split_on '\n',
pure $ do n ← ns, (ax_names.find n).to_list

meta def find_lemmas (max := 10) : tactic (list (expr × name)) := do
rgoal ← reverted_target,
axs ← timetac "Premise selection took" $ select_for_goal rgoal,
let axs := (axs.take max).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
timetac "Lemma filtering took" $ filter_lemmas axs

meta def reconstruct (axs : list expr) : tactic unit :=
focus1 $ super.with_ground_mvars $ do
axs ← list.join <$> (axs.mmap $ λ ax,
  pure <$>
      ((do const ax _ ← pure ax, mk_const ax >>= super.clause.of_proof)
      <|> (do local_const _ _ _ _ ← pure ax, super.clause.of_proof ax))
    <|> pure []),
axs ← (++ axs) <$> (tactic.local_context >>= list.mmap super.clause.of_proof),
super.solve_with_goal {} axs

-- -- set_option profiler true
-- #eval do
-- let goal : expr := `(∀ x y : nat, x < y ∨ x ≥ y),
-- let goal : expr := `(∀ x : nat, x + 0 ≤ x),
-- -- axs ← select_for_goal goal,
-- let axs := [(``nat.le_succ, ()), (``le_refl, ()), (``add_zero, ())],
-- tactic.assert `h goal,
-- tactic.intros,
-- (tptp, _) ← do_trans ((axs.take 20).map prod.fst),
-- trace tptp

end fotr2

end hammer

namespace tactic

namespace interactive

open interactive interactive.types lean.parser hammer.fotr2

private meta def find_lemmas4_core (axs : option (list name)) (max_lemmas : ℕ) :
  tactic (list (expr × name)) := do
lems ←
  match axs with
  | none := hammer.fotr2.find_lemmas max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Lemma filtering took" $
      hammer.fotr2.filter_lemmas axs
  end,
trace "\nTry:",
trace $ to_fmt "by super " ++ (to_fmt $ lems.map $ λ lem,
  match lem.1.get_app_fn, lem.2 with
  | (expr.local_const _ n _ _), _ := n
  | _, n := n
  -- | _ := default name
  end).group,
pure lems

meta def find_lemmas4 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
find_lemmas4_core axs max_lemmas,
admit

meta def hammer4 (axs : parse $ optional $ list_of ident) (max_lemmas := 100) : tactic unit := do
lems ← find_lemmas4_core axs max_lemmas,
tactic.intros,
hammer.fotr2.reconstruct (lems.map prod.fst)

end interactive
end tactic

set_option profiler true
set_option trace.super true
-- example (x y : ℕ) : x ≤ max x (y) :=
-- --  by hammer4 [le_max_iff, le_refl, le_trans]
-- by hammer4
-- -- by super [x,
-- --  le_refl,
-- --  y,
-- --  le_max_iff]
