import tactic.hammer.feature_search system.io tactic.core meta.coinductive_predicates
super

meta def format.paren' (a : format) :=
a.paren.group

meta def expr.constants (e : expr) : list name :=
native.rb_set.to_list $ e.fold native.mk_rb_set $ λ e _ s,
match e with
| (expr.const n _) := s.insert n
| _ := s
end

namespace hammer

open tactic expr native

inductive fo_term
| fn (sym : name) (args : list fo_term)
| var (sym : name)

namespace fo_term

protected meta def to_fmt : fo_term → format
| (fn s []) := _root_.to_fmt s
| (fn s as) := _root_.to_fmt s ++
  (format.paren' $ format.join $
    list.intersperse ("," ++ format.line) $ as.map to_fmt)
| (var s) := _root_.to_fmt s

meta instance : has_to_tactic_format fo_term := ⟨pure ∘ fo_term.to_fmt⟩
meta instance : has_to_format fo_term := ⟨fo_term.to_fmt⟩
meta instance : has_to_string fo_term := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr fo_term := ⟨to_string ∘ to_fmt⟩

end fo_term

def fo_term.const (sym : name) : fo_term :=
fo_term.fn sym []

inductive fo_fml
| eq (a b : fo_term)
| pred (sym : name) (args : list fo_term)
| true | false
| neg (a : fo_fml)
| and (a b : fo_fml)
| or (a b : fo_fml)
| imp (a b : fo_fml)
| iff (a b : fo_fml)
| all (x : name) (a : fo_fml)
| ex (x : name) (a : fo_fml)

namespace fo_fml

def alls : list name → fo_fml → fo_fml
| (x :: xs) a := all x (alls xs a)
| [] a := a

private meta def binop (op : string) (a : format) (b : format) : format :=
format.paren' $ a ++ format.space ++ op ++ format.line ++ b

private meta def quant (q : string) (x : name) (b : format) : format :=
format.paren' $ q ++ format.space ++ _root_.to_fmt x ++ "," ++ format.line ++ b

protected meta def to_fmt : fo_fml → format
| (eq a b) := binop "=" a.to_fmt b.to_fmt
| true := "⊤"
| false := "⊥"
| (neg a) := format.paren' $ "¬" ++ format.line ++ a.to_fmt
| (and a b) := binop "∧" a.to_fmt b.to_fmt
| (or a b) := binop "∨" a.to_fmt b.to_fmt
| (imp a b) := binop "→" a.to_fmt b.to_fmt
| (iff a b) := binop "↔" a.to_fmt b.to_fmt
| (all x a) := quant "∀" x a.to_fmt
| (ex x a) := quant "∃" x a.to_fmt
| (pred s as) := (fo_term.fn s as).to_fmt

meta instance : has_to_tactic_format fo_fml := ⟨pure ∘ fo_fml.to_fmt⟩
meta instance : has_to_format fo_fml := ⟨fo_fml.to_fmt⟩
meta instance : has_to_string fo_fml := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr fo_fml := ⟨to_string ∘ to_fmt⟩

end fo_fml

structure trans_state :=
(fresh_idx : ℕ)
(out : list (name × fo_fml))

@[reducible]
meta def trans := state_t trans_state tactic

meta def trans.run {α} (t : trans α) : tactic α :=
prod.fst <$> (show state_t _ tactic α, from t).run {
  fresh_idx := 0,
  out := [],
}

meta def trans.get_out : trans (list (name × fo_fml)) :=
do s ← state_t.get, pure s.out

meta def trans.decl_out (n : name) (f : fo_fml) : trans unit :=
state_t.modify $ λ s, { out := (n, f) :: s.out, ..s }

meta def fresh_num : trans ℕ := do
state_t.modify (λ s, { fresh_idx := s.fresh_idx + 1, ..s }),
trans_state.fresh_idx <$> state_t.get

meta def fresh_name (hint : name) : trans name :=
do n ← fresh_num, pure $ name.mk_numeral (unsigned.of_nat n) hint

def term_prf := fo_term.const ``true.intro

meta def trans_var (n : name) (t : expr) (bi : binder_info := binder_info.default) :
  trans (name × expr) := do
x' ← fresh_name n,
pure (x', local_const x' x' bi t)

private meta def contained_lconsts' : expr → rb_map name expr → rb_map name expr
| (var _) m := m
| (sort _) m := m
| (const _ _) m := m
| (mvar _ _ t) m := contained_lconsts' t m
| lc@(local_const uniq pp bi t) m := contained_lconsts' t (rb_map.insert m uniq lc)
| (app a b) m := contained_lconsts' a (contained_lconsts' b m)
| (lam _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (pi _ _ d b) m := contained_lconsts' d (contained_lconsts' b m)
| (elet _ t v b) m := contained_lconsts' t (contained_lconsts' v (contained_lconsts' b m))
| (macro _ _) m := m

meta def contained_lconsts (e : expr) : rb_map name expr :=
contained_lconsts' e (rb_map.mk name expr)

meta def contained_lconsts_list (es : list expr) : rb_map name expr :=
es.foldl (λ lcs e, contained_lconsts' e lcs) (rb_map.mk name expr)

meta def sort_lconsts : rb_map name expr → list expr | m :=
if m.empty then [] else
let next := m.filter $ λ t, ∀ x ∈ (contained_lconsts t.local_type).keys, ¬ m.contains x in
next.values ++ sort_lconsts (next.fold m (λ n _ m, m.erase n))

meta def mk_pi (lc : expr) (e : expr) : expr :=
expr.pi lc.local_pp_name lc.local_binding_info lc.local_type (e.abstract_local lc.local_uniq_name)

meta def mk_pis : list expr → expr → expr
| (x::xs) e := mk_pi x (mk_pis xs e)
| [] e := e

private def to_const {α} (a : α) : α := a

meta def mk_to_const (n : name) (t : expr) : expr :=
`(@to_const.{1} %%t %%(local_const n n binder_info.default t))

meta mutual def trans_term, trans_type, trans_fml, trans_decl
with trans_term : expr → trans fo_term | t := do
t ← state_t.lift $ zeta t,
t ← state_t.lift $ head_beta t,
t ← state_t.lift $ head_eta t,
is_proof ← state_t.lift (is_proof t),
if is_proof then pure term_prf else
match t with
| `(to_const %%(local_const n pp_n _ _)) :=
  pure $ fo_term.const pp_n
| (app a b) := do
  a' ← trans_term a,
  b' ← trans_term b,
  pure $ fo_term.fn `_A [a', b']
| (const n _) := pure $ fo_term.const n
| (sort _) := pure $ fo_term.const `_S
| (local_const n pp_n _ _) := pure $ fo_term.var pp_n
| (elet pp_n t v b) := trans_term (b.instantiate_var t)
| (mvar _ _ _) := fo_term.const <$> fresh_name `UNSUPPORTED_MVAR
| (macro _ es) :=
  fo_term.fn <$> fresh_name `UNSUPPORTED_MACRO <*> es.mmap trans_term
| (var _) := state_t.lift (fail "open term")
| (lam _ _ _ _) := do
  n ← fresh_name `_lambda,
  ty ← state_t.lift $ infer_type t,
  let lcs := sort_lconsts (contained_lconsts t),
  let n_ty := mk_pis lcs ty,
  let t' := expr.app_of_list (mk_to_const n n_ty) lcs,
  trans_decl n n_ty,
  trans_decl (n.mk_string "eqn") $ mk_pis lcs `(@eq.{1} %%ty %%t %%t'),
  trans_term t'
| (pi _ _ _ _) := do
  n ← fresh_name `_pi,
  ty ← state_t.lift $ infer_type t,
  let lcs := sort_lconsts (contained_lconsts t),
  let n_ty := mk_pis lcs ty,
  let t' := expr.app_of_list (mk_to_const n n_ty) lcs,
  trans_decl n n_ty,
  -- TODO
  -- trans_decl (n.mk_string "eqn") $ mk_pis lcs `(@eq.{1} %%ty %%t %%t'),
  trans_term t'
end
with trans_type : expr → expr → trans fo_fml | e t :=
do t_is_prop ← state_t.lift $ is_prop t,
if t_is_prop then do
  e' ← trans_term e,
  fo_fml.and (fo_fml.eq e' term_prf) <$> trans_fml t
else match t with
| (pi pp_n bi a b) := do
  a_is_prop ← state_t.lift (is_prop a),
  (x', x) ← trans_var pp_n a bi,
  if a_is_prop then do
    a' ← trans_fml a,
    b' ← trans_type (e.app a.mk_sorry) (b.instantiate_var a.mk_sorry),
    pure $ fo_fml.imp a' b'
  else do
    a' ← trans_type x a,
    b' ← trans_type (e.app x) (b.instantiate_var x),
    pure $ fo_fml.all x' $ fo_fml.imp a' b'
| _ := do e' ← trans_term e, t' ← trans_term t, pure (fo_fml.pred `_T [e', t'])
end
with trans_fml : expr → trans fo_fml | t :=
match t with
| `(@eq %%t %%(a@(expr.lam pp_n bi c _)) %%b) := do
  (x, x') ← trans_var pp_n c bi,
  a' ← state_t.lift $ tactic.head_beta $ app a x',
  b' ← state_t.lift $ tactic.head_beta $ app b x',
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x <$> (fo_fml.imp <$> trans_type x' c <*> trans_fml `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%(b@(expr.lam pp_n bi c _))) := do
  (x, x') ← trans_var pp_n c bi,
  a' ← state_t.lift $ tactic.head_beta $ app a x',
  b' ← state_t.lift $ tactic.head_beta $ app b x',
  t' ← state_t.lift $ infer_type a',
  fo_fml.all x <$> (fo_fml.imp <$> trans_type x' c <*> trans_fml `(@eq.{1} %%t' %%a' %%b'))
| `(@eq %%t %%a %%b) := trans_fml `(@heq.{1} %%t %%t %%a %%b)
| `(@heq %%t %%t' %%a %%b) := do
  t_is_prop ← state_t.lift (is_prop t),
  if t_is_prop then
    trans_fml `(%%a ↔ %%b)
  else
    fo_fml.eq <$> trans_term a <*> trans_term b
| `(%%a ∧ %%b) := fo_fml.and <$> trans_fml a <*> trans_fml b
| `(%%a ∨ %%b) := fo_fml.or <$> trans_fml a <*> trans_fml b
| `(%%a ↔ %%b) := fo_fml.iff <$> trans_fml a <*> trans_fml b
| `(Exists %%(expr.lam pp_n bi a b)) :=
  if b.has_var_idx 0 then do
    (x', x) ← trans_var pp_n a bi,
    a' ← trans_type x a,
    b' ← trans_fml (b.instantiate_var x),
    pure (fo_fml.ex x' $ fo_fml.and a' b')
  else
    fo_fml.and <$> trans_fml a <*> trans_fml b
| (pi pp_n bi a b) :=
  if b.has_var_idx 0 then do
    (x', x) ← trans_var pp_n a bi,
    a' ← trans_type x a,
    b' ← trans_fml (b.instantiate_var x),
    pure (fo_fml.all x' $ fo_fml.imp a' b')
  else
    fo_fml.imp <$> trans_fml a <*> trans_fml b
| _ := do t' ← trans_term t, pure (fo_fml.pred `_P [t'])
end
with trans_decl : name → expr → trans unit | n t := do
t_is_prop ← state_t.lift $ is_prop t,
t' ←
  if t_is_prop then
    trans_fml t
  else
    trans_type (mk_to_const n t) t,
trans.decl_out n t'

def tptpify_char : char → list char | c :=
if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ ('0' ≤ c ∧ c ≤ '9') then [c] else
match c with
| 'α' := ['_', 'g', 'a']
| 'β' := ['_', 'g', 'b']
| '₁' := ['_', 'l', '1']
| '₂' := ['_', 'l', '2']
| '_' := ['_', '_']
| '\'' := ['_', 'p']
| c := '_' :: 'u' ::
  (list.range 6).reverse.map (λ i, (c.val / 16^i % 16).digit_char)
end

def tptpify_string (s : string) : string :=
(s.to_list >>= tptpify_char).as_string

meta def tptpify_name : name → string
| name.anonymous := ""
| (name.mk_string s name.anonymous) := tptpify_string s
| (name.mk_numeral i name.anonymous) := to_string i
| (name.mk_string s n) := tptpify_name n ++ "_o_" ++ tptpify_string s
| (name.mk_numeral s n) := tptpify_name n ++ "_n" ++ to_string s

meta def fn_tptpify_name : name → string
| `_T := "t"
| `_S := "s"
| `_A := "a"
| `_P := "p"
| n := "c" ++ tptpify_name n

meta def var_tptpify_name (n : name) : string :=
"X" ++ tptpify_name n

meta def ax_tptpify_name (n : name) : string :=
fn_tptpify_name n

meta def tptpify_term : fo_term → format
| (fo_term.fn s []) := fn_tptpify_name s
| (fo_term.fn s as) := format.group $ fn_tptpify_name s ++
  format.paren (format.join $ list.intersperse ("," ++ format.line) $ as.map tptpify_term)
| (fo_term.var s) := var_tptpify_name s

meta def tptpify_binop (op : string) (a : format) (b : format) : format :=
format.paren' $ a ++ format.space ++ op ++ format.line ++ b

meta def tptpify_quant (q : string) (x : name) (b : format) : format :=
format.paren' $ q ++ "[" ++ var_tptpify_name x ++ "]:" ++ format.line ++ b

section open fo_fml
meta def tptpify_fml : fo_fml → format
| (eq a b) := tptpify_binop "=" (tptpify_term a) (tptpify_term b)
| true := "$true"
| false := "$false"
| (neg a) := format.paren' $ "~" ++ format.line ++ (tptpify_fml a)
| (and a b) := tptpify_binop "&" (tptpify_fml a) (tptpify_fml b)
| (or a b) := tptpify_binop "|" (tptpify_fml a) (tptpify_fml b)
| (imp a b) := tptpify_binop "=>" (tptpify_fml a) (tptpify_fml b)
| (iff a b) := tptpify_binop "<=>" (tptpify_fml a) (tptpify_fml b)
| (all x a) := tptpify_quant "!" x (tptpify_fml a)
| (ex x a) := tptpify_quant "?" x (tptpify_fml a)
| (pred s as) := tptpify_term (fo_term.fn s as)
end

meta def tptpify_ann (role : string) (n : name) (f : fo_fml) : format :=
format.group $ format.nest 1 $ "fof(" ++ format.group (
    ax_tptpify_name n ++ "," ++ format.line ++ role ++ ",")
  ++ format.line ++ tptpify_fml f ++ ")."

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
    cs ← (do d ← get_decl n, pure $ some $ d.type.constants.filter is_good_const) <|> pure none,
    match cs with
    | none := close_under_references_core ns s
    | some cs := close_under_references_core (cs ++ ns) (s.insert n)
    end

meta def close_under_references (ns : list name) : tactic (list name) :=
rb_set.to_list <$> close_under_references_core ns mk_rb_set

meta def close_under_instances (ns : list name) : tactic (list name) := do
let ns : rb_set name := rb_map.set_of_list ns,
e ← get_env,
ds ← e.get_trusted_decls.mfilter (λ d, is_instance d.to_name),
il ← mk_ignore_args,
let ds := ds.filter (λ d, ∀ c ∈ (non_ignored_consts il d.type mk_name_set).to_list, ns.contains c),
-- trace $ ds.map (λ d, d.to_name),
pure $ rb_set.to_list $ ds.foldl (λ ns d, ns.insert d.to_name) ns

meta def trans_decl' (d : declaration) : trans unit := do
t_is_prop ← state_t.lift $ tactic.is_prop d.type,
trans_decl d.to_name d.type,
pure ()
-- when (¬ t_is_prop ∧ d.is_definition) $ do
--   let eqn_ty :=
--     `(@eq.{1} %%d.type %%(expr.const d.to_name (d.univ_params.map level.param)) %%d.value),
--   state_t.lift $ trace eqn_ty,
--   state_t.lift $ infer_type eqn_ty,
--   trans_decl (d.to_name.mk_string "_dfn") eqn_ty

meta def mk_h_defeq (e1 e2 : expr) (t1 t2 : expr) : tactic expr := do
(xs1, t1) ← mk_meta_pis t1,
(xs2, t2) ← mk_meta_pis t2,
unify t1 t2,
let e1 := e1.app_of_list xs1,
let e2 := e2.app_of_list xs2,
unify e1 e2,
e1 ← instantiate_mvars e1,
e2 ← instantiate_mvars e2,
guard $ ¬ e1.has_meta_var ∧ ¬ e2.has_meta_var,
mk_app ``eq [e1, e2]

meta def mk_h_defeq_decl (n1 n2 : name) : tactic expr := do
(e1, t1) ← get_decl n1 >>= decl_mk_const,
(e2, t2) ← get_decl n2 >>= decl_mk_const,
mk_h_defeq e1 e2 t1 t2

#eval mk_h_defeq_decl ``nat.semiring ``comm_semiring.to_semiring >>= trace

meta def add_instance_defeq (i1 i2 : name) : trans unit :=
(do eqn ← state_t.lift $ mk_h_defeq_decl i1 i2,
    n ← fresh_name `_instance_defeq,
    trans_decl n eqn
) <|> pure ()

meta def add_instance_defeqs (axs : list name) : trans unit := do
is ← state_t.lift $ axs.mfilter is_instance,
monad.sequence' $ do
  i1 ← is,
  i2 ← is,
  guard $ i1 < i2,
  [add_instance_defeq i1 i2]

meta def do_trans (axs : list name) (goal : expr) : tactic (format × list (string × name)) := trans.run $ do
let axs := goal.constants.filter is_good_const ++ axs,
axs ← state_t.lift $ close_under_references axs,
axs ← state_t.lift $ close_under_instances axs,
axs ← state_t.lift $ close_under_references axs,
state_t.lift $ trace $ (axs.map name.to_string).qsort (λ a b, a < b),
axs.mmap' (λ n, do d ← state_t.lift $ get_decl n, trans_decl' d),
add_instance_defeqs axs,
goal_is_prop ← state_t.lift $ tactic.is_prop goal,
goal' ← if goal_is_prop then trans_fml goal
  else (do (x,x') ← trans_var `_goal goal, fo_fml.all x <$> trans_type x' goal),
out ← trans.get_out,
let anns := out.map $ λ ⟨n, f⟩, tptpify_ann "axiom" n f,
let anns := (tptpify_ann "conjecture" `_goal goal') :: anns,
let tptp := format.join $ list.intersperse (format.line ++ format.line) anns.reverse,
pure (tptp, out.map (λ ⟨n, _⟩, (ax_tptpify_name n, n)))

-- #eval do_trans [
--   ``nat.prod_dvd_and_dvd_of_dvd_prod,
-- --  ``heq.drec_on,
--  ``nat.exists_coprime
-- ] `(
--   ∀ {m n : ℕ} (H : 0 < nat.gcd m n),
--   ∃ g m' n', 0 < g ∧ nat.coprime m' n' ∧ m = m' * g ∧ n = n' * g
-- ) >>= tactic.trace

section

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
exec_cmd "vampire" ["-p", "tptp"] tptp

end

meta def filter_lemmas1 (axs : list name) (goal : expr) : tactic (list name) := do
(tptp, ax_names) ← do_trans axs goal,
(tactic.unsafe_run_io $ do f ← io.mk_file_handle "hammer.p" io.mode.write, io.fs.write f tptp.to_string.to_char_buffer, io.fs.close f),
let ax_names := rb_map.of_list ax_names,
tptp_out ← exec_cmd "bash" ["-c",
  "vampire -p tptp -t 30s --output_axiom_names on | " ++
    "grep -oP '(?<=file\\(unknown,).*?(?=\\))'"]
  tptp.to_string,
let ns := tptp_out.split_on '\n',
pure $ do n ← ns, (ax_names.find n).to_list

meta def find_lemmas1 (goal : expr) (max := 10) : tactic (list name) := do
axs ← timetac "Premise selection took" $ select_for_goal goal,
let axs := (axs.take max).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
timetac "Vampire took" $ filter_lemmas1 axs goal

meta def reconstruct1 (axs : list name) : tactic unit :=
focus1 $ super.with_ground_mvars $ do
axs ← list.join <$> (axs.mmap $ λ ax,
  pure <$> (mk_const ax >>= super.clause.of_proof) <|> pure []),
super.solve_with_goal {} axs

#eval do
let goal : expr := `(∀ x y : nat, x < y ∨ x ≥ y),
let goal : expr := `(∀ x : nat, x ≤ x),
-- axs ← select_for_goal goal,
let axs := [(``nat.le_succ, ()), (``le_refl, ())],
(tptp, _) ← do_trans ((axs.take 20).map prod.fst) goal,
trace tptp

end hammer

namespace tactic

namespace interactive

open interactive interactive.types lean.parser

meta def find_lemmas1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
goal ← reverted_target,
lems ←
  match axs with
  | none := hammer.find_lemmas1 goal max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Vampire took" $
      hammer.filter_lemmas1 axs goal
  end,
trace "Vampire proof uses the following lemmas:",
lems.mmap' $ λ l, trace $ "  " ++ l.to_string,
admit

meta def hammer1 (axs : parse $ optional $ list_of ident) (max_lemmas := 10) : tactic unit := do
goal ← reverted_target,
lems ←
  match axs with
  | none := hammer.find_lemmas1 goal max_lemmas
  | some axs := do
    axs.mmap' (λ ax, get_decl ax),
    timetac "Vampire took" $
      hammer.filter_lemmas1 axs goal
  end,
trace "Vampire proof uses the following lemmas:",
lems.mmap' $ λ l, trace $ "  " ++ l.to_string,
tactic.intros,
hammer.reconstruct1 lems

end interactive
end tactic
