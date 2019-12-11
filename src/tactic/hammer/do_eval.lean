import tactic.hammer.monomorphization tactic.suggest

namespace hammer
open tactic

meta def eval_library_search (for_env : environment) (_ : string) : tactic unit := do
set_env_core for_env,
library_search >>= trace,
skip

meta def eval_simp (for_env : environment) (_ : string) : tactic unit := do
set_env_core for_env,
intros,
`[simp *],
done

meta def eval_hammer1 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
goal ← reverted_target,
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> select_for_goal goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas1 axs goal,
trace "Vampire proof uses the following lemmas:",
lems.mmap' $ λ l, trace $ "  " ++ l.to_string,
tactic.intros,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct1 lems

meta def eval_hammer2 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> revert_all >> target >>= select_for_goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
-- trace "Premise selection:",
trace axs,
(tptp, ax_names) ← timetac ("MONOM " ++ desc) $ mk_monom_file axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas2_core tptp ax_names,
-- lems ← retrieve (do set_env_core for_env, hammer.find_lemmas2 max_lemmas),
trace "eprover-ho proof uses the following lemmas:",
lems.mmap' (λ ⟨l, t⟩, do
  l' ← pp l,
  -- t ← infer_type l >>= pp,
  t ← pp t,
  trace (format.nest 4 $ format.group $ "  " ++ l' ++ " :" ++ format.line ++ t)),
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct2 lems

meta def my_timetac (desc : string) (tac : string → tactic unit) (time_limit := 100000) : tactic unit :=
timetac ("TOTAL " ++ desc) $ do
trace $ "START " ++ desc,
s ← read,
match try_for time_limit (tac desc) s with
| result.exception msg _ _ := do
  trace $ "FAIL " ++ desc,
  trace $ msg.get_or_else (λ _, to_fmt "") ()
| _ :=
  trace $ "SUCCESS " ++ desc
end

meta def do_eval_core (env : environment) (n : name) : tactic unit := do
trace $ ">>> " ++ to_string n,
my_timetac (to_string n ++ " library_search 0") (eval_library_search env),
my_timetac (to_string n ++ " simp 0") (eval_simp env),
my_timetac (to_string n ++ " hammer1 10") (eval_hammer1 env 10),
my_timetac (to_string n ++ " hammer2 10") (eval_hammer2 env 10),
my_timetac (to_string n ++ " hammer2 100") (eval_hammer2 env 100),
skip

meta def do_eval_for_thm (decl_name : name) : tactic unit := retrieve $ do
unfreeze_local_instances,
e ← get_env,
some lean_file ← pure $ e.decl_olean decl_name,
decl ← get_decl decl_name,
goal ← mk_meta_var decl.type,
set_goals [goal], intros,
trace_state,
let env_for_thm := environment.for_decl_of_imported_module lean_file decl_name,
do_eval_core env_for_thm decl_name

-- #eval do_eval_for_thm ``inv_mul_cancel_left

end hammer
