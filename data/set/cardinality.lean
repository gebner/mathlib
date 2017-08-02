import data.set.basic
import algebra.lattice.fixed_points
import data.set.lattice
import data.set.classical_inverse
universes u v

namespace function

variables {α β : Type u} {f : α → β} (fbij : bijective f)

noncomputable def bijective.inv : β → α
| b := classical.some (fbij.right b)

lemma bijective_inv_spec (b : β) : f (fbij.inv b) = b :=
classical.some_spec (fbij.right b)

private lemma bijective_inv_inj : injective fbij.inv :=
begin
intros b1 b2 b1eqb2,
have fb1eqb2: f (bijective.inv fbij b1) = f (bijective.inv fbij b2), {cc},
simp [bijective_inv_spec fbij] at fb1eqb2, assumption
end

private lemma bijective_inv_surj : surjective fbij.inv :=
by intro a; existsi f a; apply fbij.left; simp [bijective_inv_spec fbij]

lemma bijective_inv_bijective : bijective fbij.inv :=
⟨bijective_inv_inj _, bijective_inv_surj _⟩

end function

open function

def set.dominated_by (α β : Type u) : Prop :=
∃ f : α → β, injective f

local infix ` ≼ `:50 := set.dominated_by

def set.equinumerous (α β : Type u) : Prop :=
∃ f : α → β, bijective f

local infix ` ≅ `:50 := set.equinumerous

namespace set
variables {α β γ : Type u}

@[refl,simp] lemma dominated_by_refl : α ≼ α :=
⟨id, injective_id⟩

@[trans] lemma dominated_by_trans : α ≼ β → β ≼ γ → α ≼ γ
| ⟨fab, iab⟩ ⟨fbc, ibc⟩ := ⟨fbc ∘ fab, injective_comp ibc iab⟩

@[refl,simp] lemma equinumerous.refl : α ≅ α :=
⟨id, bijective_id⟩

@[symm] lemma equinumerous.symm : α ≅ β → β ≅ α
| ⟨f, fbij⟩ := ⟨fbij.inv, bijective_inv_bijective _⟩

@[trans] lemma equinumerous.trans : α ≅ β → β ≅ γ → α ≅ γ
| ⟨f, fbij⟩ ⟨g, gbij⟩ := ⟨g ∘ f, bijective_comp gbij fbij⟩

lemma dominated_eqn_congr {α α' β β' : Type v} :
    α' ≅ α → β ≅ β' → α ≼ β → α' ≼ β'
| ⟨f, finj, _⟩ ⟨g, ginj, _⟩ ⟨h, hinj⟩ :=
    ⟨g ∘ h ∘ f, injective_comp ginj (injective_comp hinj finj)⟩

def sum.map {α α' : Type u} {β β' : Type v}
    (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr (g b)

@[congr]
lemma equinumerous.congr_sum {α α' : Type u} {β β' : Type v} :
    α ≅ α' → β ≅ β' → (α ⊕ β) ≅ (α' ⊕ β') | ⟨f, fbij⟩ ⟨g, gbij⟩ :=
⟨sum.map f g, begin
intros a b, cases a; cases b; simp [sum.map]; intro h; injection h; tactic.congr,
apply fbij.left, assumption, apply gbij.left, assumption
end, begin
intro c, cases c with a b,
{cases fbij.right a with a aspec, existsi sum.inl a, simp [sum.map, *] },
{cases gbij.right b with b bspec, existsi sum.inr b, simp [sum.map, *] }
end⟩

def sum.swap {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α
| (sum.inl a) := sum.inr a
| (sum.inr b) := sum.inl b

lemma equinumerous.sum_comm {α : Type u} {β : Type v} :
    (α ⊕ β) ≅ (β ⊕ α) :=
⟨sum.swap, begin
intros a b, cases a; cases b; simp [sum.swap]; intro h; injection h; simp*,
end, begin
intro c, cases c with a b,
{existsi sum.inr a, simp [sum.swap, *] },
{existsi sum.inl b, simp [sum.swap, *] }
end⟩

local attribute [instance] classical.prop_decidable
lemma equinumerous.disjoint_union {α : Type u} {X : set α} :
    α ≅ ({a // a ∈ X} ⊕ {a // a ∉ X}) :=
⟨λ a, if h : a ∈ X then sum.inl ⟨a,h⟩ else sum.inr ⟨a,h⟩,
begin
    intros a b,
    by_cases a ∈ X with ax; by_cases b ∈ X with bx;
    simp*; intro h; repeat {injection h},
end,
begin
    intros a, cases a with a a; cases a with a ax; existsi a; simp*,
end⟩

end set

namespace set.cantor_schroeder_bernstein
open set
section
parameters {α β : Type u} (f : α → β) (g : β → α)

def phi (x : set α) : set α :=
g '' -(f '' -x)

lemma phi_monotone : monotone phi :=
begin
intros x y xiny,
apply image_subset, apply compl_subset,
apply image_subset, apply compl_subset,
assumption
end

def X := lattice.lfp phi

lemma X_spec : X = g '' -(f '' -X) :=
show X = phi X, by unfold X; rw [←lattice.lfp_eq (phi_monotone f g)]

local attribute [instance] classical.prop_decidable

def h1inv : {b // b ∈ -(f '' -X)} → {a // a ∈ X} | ⟨b, bnfnx⟩ :=
⟨g b, begin rw X_spec, apply mem_image bnfnx rfl end⟩

lemma h1inv_inj (ginj : injective g) : injective h1inv
| ⟨a, anfnx⟩ ⟨b, bnfnx⟩ gaeqgb := begin
injection gaeqgb with gaeqgb, tactic.congr,
apply ginj, assumption,
end

lemma h1inv_surj : surjective h1inv | ⟨a, ax⟩ :=
begin
rw X_spec at ax, cases ax with b bspec,
refine ⟨⟨b, bspec.left⟩, _⟩,
unfold h1inv, tactic.congr, apply bspec.right
end

lemma part1 (ginj: injective g) : {b // b ∈ -(f '' -X)} ≅ {a // a ∈ X} :=
⟨h1inv, h1inv_inj ginj, h1inv_surj⟩

def h2 : {a // a ∈ -X} → {b // b ∈ f '' -X} | ⟨a, hnx⟩ :=
⟨f a, mem_image hnx rfl⟩

lemma h2_inj (finj : injective f) : injective h2
| ⟨a, anx⟩ ⟨b, bnx⟩ faeqfb := begin
tactic.congr, injection faeqfb with faeqfb,
apply finj, assumption
end

lemma h2_surj : surjective h2 | ⟨b, bfnx⟩ := begin
cases bfnx with a aspec,
refine ⟨⟨a, aspec.left⟩, _⟩,
unfold h2, tactic.congr, apply aspec.right
end

lemma part2 (finj: injective f) : {a // a ∈ -X} ≅ {b // b ∈ f '' -X} :=
⟨h2, h2_inj finj, h2_surj⟩

lemma eqn (finj : injective f) (ginj : injective g) : α ≅ β :=
calc α ≅ ({a // a ∈ X} ⊕ {a // a ∉ X}) : equinumerous.disjoint_union
   ... ≅ ({b // b ∈ -(f '' -X)} ⊕ {b // b ∈ f '' -X}) :
            equinumerous.congr_sum (part1 ginj).symm (part2 finj)
   ... ≅ ({b // b ∈ f '' -X} ⊕ {b // b ∈ -(f '' -X)}) : equinumerous.sum_comm
   ... ≅ β : equinumerous.disjoint_union.symm

end
end set.cantor_schroeder_bernstein

namespace set
variables {α β γ : Type u}

lemma cantor_schroeder_bernstein : α ≼ β → β ≼ α → α ≅ β
| ⟨f, finj⟩ ⟨g, ginj⟩ := set.cantor_schroeder_bernstein.eqn _ _ finj ginj

protected lemma equinumerous.dominates : α ≅ β → α ≼ β
| ⟨f, finj, fsurj⟩ := ⟨f, finj⟩

end set

namespace set

@[instance] def equinumerosity_setoid : setoid (Type u) :=
{ r := (≅),
  iseqv := ⟨@equinumerous.refl, @equinumerous.symm, @equinumerous.trans⟩ }

def cardinality : Type (u+1) :=
quotient equinumerosity_setoid

def card (α : Type u) : cardinality := ⟦α⟧

namespace cardinality

protected def le (a b : cardinality) : Prop :=
quotient.lift₂ (≼) (begin
    intros; apply propext; split; apply dominated_eqn_congr;
    try { assumption <|> `[apply equinumerous.symm; assumption] }
end) a b

protected def has_le : has_le cardinality := ⟨cardinality.le⟩
local attribute [instance] cardinality.has_le

instance : linear_strong_order_pair cardinality.{u} := {
    le := cardinality.le,
    lt := λ a b, a ≤ b ∧ a ≠ b,
    le_refl := quotient.ind begin intro a, apply dominated_by_refl end,
    le_trans := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        refine quotient.ind _, intro c,
        apply dominated_by_trans
    end,
    le_antisymm := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        intros ab ba,
        apply quotient.sound,
        apply cantor_schroeder_bernstein; assumption
    end,
    le_iff_lt_or_eq :=
    begin
        intros a b, change a ≤ b ↔ ((a ≤ b ∧ a ≠ b) ∨ a = b), split; intro h,
        { cases classical.prop_decidable (a = b),
         {left, split; assumption}, {right, assumption} },
        {cases h with h h, apply h.left, subst h,
         revert a, refine quotient.ind _, intro a,
         apply dominated_by_refl }
    end,
    lt_irrefl := λ a alta, alta.right rfl,
    le_total := _,
}

end cardinality

end set