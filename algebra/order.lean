/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
open eq function

/- TODO: automatic construction of dual definitions / theorems -/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section monotone
variables [preorder α] [preorder β] [preorder γ]

def monotone (f : α → β) := ∀{{a b}}, a ≤ b → f a ≤ f b

theorem monotone_id : @monotone α α _ _ id := assume x y h, h

theorem monotone_const {b : β} : monotone (λ(a:α), b) := assume x y h, le_refl b

theorem monotone_comp {f : α → β} {g : β → γ} (m_f : monotone f) (m_g : monotone g) :
  monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

end monotone

section strictly_monotone
variables [preorder α] [preorder β] [preorder γ]

def strictly_monotone (f : α → β) := ∀{{a b}}, a < b → f a < f b

lemma strictly_monotone_id : @strictly_monotone α α _ _ id := assume x y h, h

lemma strictly_monotone_comp {f : α → β} {g : β → γ} (m_f : strictly_monotone f) (m_g : strictly_monotone g) :
  strictly_monotone (g ∘ f) :=
assume a b h, m_g (m_f h)

end strictly_monotone

lemma injective_of_strictly_monotone {α β} [linear_order α] [preorder β] {f : α → β} (m : strictly_monotone f) : function.injective f :=
assume a b heq, match lt_trichotomy a b with
| or.inl hlt :=
  have f a < f b, from m hlt,
  have f a ≠ f b, from ne_of_lt this,
  false.elim (this heq)
| or.inr (or.inl heq) := heq
| or.inr (or.inr hgt) :=
  have f b < f a, from m hgt,
  have f a ≠ f b, from (ne_of_lt this).symm,
  false.elim (this heq)
end

section
  variable [decidable_linear_order α]
  variables {a b c d : α}
  open decidable

  theorem le_max_left_iff_true (a b : α) : a ≤ max a b ↔ true :=
  iff_true_intro (le_max_left a b)

  theorem le_max_right_iff_true (a b : α) : b ≤ max a b ↔ true :=
  iff_true_intro (le_max_right a b)

  theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c

  theorem max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c

  theorem max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c
end

/- order instances -/

instance preorder_fun [preorder β] : preorder (α → β) :=
{ le := λx y, ∀b, x b ≤ y b,
  le_refl := λf b, le_refl (f b),
  le_trans := λf g h h1 h2 b, le_trans (h1 b) (h2 b),
}

instance partial_order_fun [partial_order β] : partial_order (α → β) :=
{ preorder_fun with
  le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b))
}

def weak_order_dual (wo : partial_order α) : partial_order α :=
{ le := λx y, y ≤ x,
  le_refl := le_refl,
  le_trans := assume a b c h₁ h₂, le_trans h₂ h₁,
  le_antisymm := assume a b h₁ h₂, le_antisymm h₂ h₁ }

theorem le_dual_eq_le {α : Type} (wo : partial_order α) (a b : α) :
  @has_le.le _ (@preorder.to_has_le _ (@partial_order.to_preorder _ (weak_order_dual wo))) a b =
  @has_le.le _ (@preorder.to_has_le _ (@partial_order.to_preorder _ wo)) b a :=
rfl

theorem comp_le_comp_left_of_monotone [preorder α] [preorder β] [preorder γ]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) : has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
assume x, m_f (le_gh x)

section monotone
variables [preorder α] [preorder γ]

theorem monotone_lam {f : α → β → γ} (m : ∀b, monotone (λa, f a b)) : monotone f :=
assume a a' h b, m b h

theorem monotone_app (f : β → α → γ) (b : β) (m : monotone (λa b, f b a)) : monotone (f b) :=
assume a a' h, m h b

end monotone

namespace preorder
variables [preorder α]

section

def equiv (a b : α) : Prop :=
a ≤ b ∧ b ≤ a

local infix ` ≃ `:50 := equiv

private lemma equiv_refl (a : α) : a ≃ a :=
⟨by refl, by refl⟩

private lemma equiv_symm (a b : α) : a ≃ b → b ≃ a
| ⟨h1, h2⟩ := ⟨h2, h1⟩

private lemma equiv_trans (a b c : α) : a ≃ b → b ≃ c → a ≃ c
| ⟨h1, h2⟩ ⟨g1, g2⟩ := ⟨_root_.le_trans h1 g1, _root_.le_trans g2 h2⟩

protected lemma equivalence_equiv : equivalence (equiv : α → α → Prop) :=
⟨equiv_refl, equiv_symm, equiv_trans⟩

protected def setoid : setoid α :=
{ r := equiv, iseqv := preorder.equivalence_equiv }

end

local attribute [instance] preorder.setoid

variables (a1 b1 a2 b2 : α)

lemma equiv_congr_le : (a1 ≈ a2) → (b1 ≈ b2) → (a1 ≤ b1 ↔ a2 ≤ b2)
| ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ :=
begin
split; intro h,
{transitivity, assumption, transitivity, apply h, assumption},
{transitivity, assumption, transitivity, apply h, assumption},
end

end preorder
