import tactic.hammer tactic.suggest tactic.finish tactic.tidy

namespace hammer
open tactic

meta def eval_refl (_ : string) : tactic unit :=
`[intros, exact rfl <|> exact iff.rfl]

meta def eval_library_search (for_env : environment) (_ : string) : tactic unit := do
set_env_core for_env,
library_search >>= trace,
skip

meta def eval_finish (for_env : environment) (_ : string) : tactic unit := do
set_env_core $
  if for_env.contains ``tactic.interactive.finish then for_env else
  for_env.import' (module_info.of_module_name `tactic.finish),
`[finish],
done

meta def eval_tidy (for_env : environment) (_ : string) : tactic unit := do
set_env_core for_env,
`[tidy],
done

meta def eval_simp (for_env : environment) (_ : string) : tactic unit := do
set_env_core for_env,
intros,
`[simp *],
done

meta def eval_hammer1 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
goal ← reverted_target,
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> select_for_goal goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas1 axs goal,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
tactic.intros,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct1 lems

meta def eval_hammer1_oracle (for_env : environment) (axs : list name) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
goal ← reverted_target,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas1 axs goal,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
tactic.intros,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct1 lems

meta def eval_hammer2 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> revert_all >> target >>= select_for_goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
(tptp, ax_names) ← timetac ("MONOM " ++ desc) $ mk_monom_file axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas2_core tptp ax_names,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct2 lems

meta def eval_hammer2_oracle (for_env : environment) (axs : list name) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
(tptp, ax_names) ← timetac ("MONOM " ++ desc) $ mk_monom_file axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas2_core tptp ax_names,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct2 lems

meta def eval_hammer3 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> revert_all >> target >>= select_for_goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
(tptp, ax_names) ← timetac ("MONOM " ++ desc) $ mk_monom2_file axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas3_core tptp ax_names,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct3 lems

meta def eval_hammer3_oracle (for_env : environment) (axs : list name) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
(tptp, ax_names) ← timetac ("MONOM " ++ desc) $ mk_monom2_file axs,
lems ← timetac ("PROVER " ++ desc) $ filter_lemmas3_core tptp ax_names,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
timetac ("RECONSTRUCT " ++ desc) $ hammer.reconstruct3 lems

meta def eval_hammer4 (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> reverted_target >>= select_for_goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
lems ← timetac ("PROVER " ++ desc) $ fotr2.filter_lemmas axs,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
tactic.intros,
timetac ("RECONSTRUCT " ++ desc) $ fotr2.reconstruct lems

meta def eval_hammer4_oracle (for_env : environment) (axs : list name) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
lems ← timetac ("PROVER " ++ desc) $ fotr2.filter_lemmas axs,
trace lems,
trace $ "NUM_PROVER_LEMMAS " ++ desc ++ " " ++ to_string lems.length,
tactic.intros,
timetac ("RECONSTRUCT " ++ desc) $ fotr2.reconstruct lems

meta def eval_super (for_env : environment) (max_lemmas : ℕ) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
goal ← retrieve (revert_all >> target),
axs ← timetac ("SELECT " ++ desc) $ retrieve $
  set_env_core for_env >> select_for_goal goal,
let axs := (axs.take max_lemmas).map (λ a, a.1),
trace axs,
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
let axs := goal.constants.filter is_good_const ++ axs,
axs ← close_under_references axs,
repeat (intro1 >> skip),
(do tgt ← target, when (tgt ≠ `(false)) $
  mk_mapp ``classical.by_contradiction [some tgt] >>= eapply >> intro1 >> skip),
lems ← (++) <$> axs.mmap mk_const <*> local_context,
timetac ("PROVER " ++ desc) $
focus1 $ super.with_ground_mvars $ do
lems ← lems.mmap super.clause.of_proof,
super.solve_with_goal {} lems

meta def eval_super_oracle (for_env : environment) (axs : list name) (desc : string) : tactic unit := do
set_env_core $ for_env.import_dependencies $ module_info.of_module_name `super,
goal ← retrieve (revert_all >> target),
trace $ "NUM_LEMMAS " ++ desc ++ " " ++ to_string axs.length,
let axs := goal.constants.filter is_good_const ++ axs,
axs ← close_under_references axs,
repeat (intro1 >> skip),
(do tgt ← target, when (tgt ≠ `(false)) $
  mk_mapp ``classical.by_contradiction [some tgt] >>= eapply >> intro1 >> skip),
lems ← (++) <$> axs.mmap mk_const <*> local_context,
timetac ("PROVER " ++ desc) $
focus1 $ super.with_ground_mvars $ do
lems ← lems.mmap super.clause.of_proof,
super.solve_with_goal {} lems

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
proof ← declaration.value <$> get_decl n,
let cs := proof.constants,
trace cs,
trace $ "PROOF_NUM_LEMMAS " ++ to_string cs.length,
trace $ "PROOF_SIZE " ++ to_string proof.get_weight,
my_timetac (to_string n ++ " refl 0") eval_refl,
my_timetac (to_string n ++ " library_search 0") (eval_library_search env),
my_timetac (to_string n ++ " finish 0") (eval_finish env),
my_timetac (to_string n ++ " tidy 0") (eval_tidy env),
my_timetac (to_string n ++ " simp 0") (eval_simp env),
my_timetac (to_string n ++ " super 10") (eval_super env 10),
my_timetac (to_string n ++ " super oracle") (eval_super_oracle env cs),
my_timetac (to_string n ++ " hammer1 10") (eval_hammer1 env 10),
my_timetac (to_string n ++ " hammer1 100") (eval_hammer1 env 100),
my_timetac (to_string n ++ " hammer1 oracle") (eval_hammer1_oracle env cs),
my_timetac (to_string n ++ " hammer2 10") (eval_hammer2 env 10),
my_timetac (to_string n ++ " hammer2 100") (eval_hammer2 env 100),
my_timetac (to_string n ++ " hammer2 oracle") (eval_hammer2_oracle env cs),
my_timetac (to_string n ++ " hammer3 10") (eval_hammer3 env 10),
my_timetac (to_string n ++ " hammer3 100") (eval_hammer3 env 100),
my_timetac (to_string n ++ " hammer3 oracle") (eval_hammer3_oracle env cs),
my_timetac (to_string n ++ " hammer4 10") (eval_hammer4 env 10),
my_timetac (to_string n ++ " hammer4 100") (eval_hammer4 env 100),
my_timetac (to_string n ++ " hammer4 oracle") (eval_hammer4_oracle env cs),
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
