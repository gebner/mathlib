import all tactic.hammer.feature_search

attribute [inline] decidable.to_bool bool.decidable_eq

meta def declaration.is_equation_lemma (decl : declaration) : bool :=
match decl.to_name with
| (name.mk_string s _) := "_eqn".is_prefix_of s
| _ := ff
end

meta def environment.list_theorems (env : environment) : list name := do
decl ← env.get_trusted_decls,
guard $ ¬ decl.is_axiom,
guard $ ¬ decl.is_constant,
guard $ decl.is_theorem,
guard $ ¬ decl.is_auto_generated env,
guard $ ¬ decl.is_equation_lemma,
let n := decl.to_name,
guard $ ¬ n.has_suffix "_sunfold",
guard $ ¬ n.has_suffix "_main",
pure decl.to_name

open tactic

meta def mod_name_of_lean_file (s : string) : name :=
name.from_components $
  (((s.popn_back 5).split (= '/'))
    .reverse.take_while (λ comp, comp ≠ "library" ∧ comp ≠ "src")).reverse

meta def mod_name_of_decl (e : environment) (n : name) : name :=
mod_name_of_lean_file ((e.decl_olean n).get_or_else "")

def string.map (f : char → char) (s : string) : string :=
(s.to_list.map f).as_string

#eval do
e ← get_env,
e.list_theorems.mmap' $ λ n, do
  let mod_name := mod_name_of_decl e n,
  let fn := (to_string mod_name ++ ".." ++ to_string n).map
    (λ c, if c = '\'' ∨ c = '/' then '_' else c) ++ ".lean",
  trace $ "echo \"import " ++ to_string mod_name ++ " tactic.hammer.do_eval " ++
    "#eval hammer.do_eval_for_thm ``" ++ to_string n ++ "\" >" ++ fn
