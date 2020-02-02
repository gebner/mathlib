import data.nat.prime tactic.hammer

open nat tactic

lemma foo {p m a : ℕ} (pp : prime p) (h : ¬ p ∣ a) : coprime a (p^m) :=
begin
  (do e ← get_env,
      let decl := ``nat.prime.coprime_pow_of_not_dvd,
      set_env_core $
        (environment.for_decl_of_imported_module ((e.decl_olean decl).get_or_else "") decl
          ).import' (module_info.of_module_name `tactic.hammer)),
  hammer3 50
end

#print foo
