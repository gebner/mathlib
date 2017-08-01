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

namespace set
variables {α β γ : Type u}

def dominated_by (α β : Type u) : Type u :=
Σ' f : α → β, injective f

infix ` ≼ `:50 := dominated_by

@[refl] def dominated_by_refl : α ≼ α :=
⟨id, injective_id⟩

@[trans] def dominated_by_trans : α ≼ β → β ≼ γ → α ≼ γ
| ⟨fab, iab⟩ ⟨fbc, ibc⟩ := ⟨fbc ∘ fab, injective_comp ibc iab⟩

def equinumerous (α β : Type u) : Type u :=
Σ' f : α → β, Σ' g : β → α, (∀ b, f (g b) = b) ∧ (∀ a, g (f a) = a)

infix ` ≅ `:50 := equinumerous

@[refl] def equinumerous.refl : α ≅ α :=
⟨id, id, λ _, rfl, λ _, rfl⟩

@[symm] def equinumerous.symm : α ≅ β → β ≅ α
| ⟨f, g, fg, gf⟩ := ⟨g, f, gf, fg⟩

@[trans] def equinumerous.trans : α ≅ β → β ≅ γ → α ≅ γ
| ⟨f1, g1, fg1, gf1⟩ ⟨f2, g2, fg2, gf2⟩ :=
    ⟨f2 ∘ f1, g1 ∘ g2,
    by intro; simp [function.comp, *],
    by intro; simp [function.comp, *]⟩

def sum.map {α α' : Type u} {β β' : Type v}
    (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr (g b)

@[congr]
def equinumerous.congr_sum {α α' : Type u} {β β' : Type v} :
    α ≅ α' → β ≅ β' → (α ⊕ β) ≅ (α' ⊕ β') | ⟨f1, g1, fg1, gf1⟩ ⟨f2, g2, fg2, gf2⟩ :=
⟨sum.map f1 f2, sum.map g1 g2,
    by intro b; cases b; simp [*, sum.map],
    by intro a; cases a; simp [*, sum.map]⟩

def sum.swap {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α
| (sum.inl a) := sum.inr a
| (sum.inr b) := sum.inl b

def equinumerous.sum_comm {α : Type u} {β : Type v} :
    (α ⊕ β) ≅ (β ⊕ α) :=
⟨sum.swap, sum.swap,
    by intro b; cases b; simp [*, sum.swap],
    by intro a; cases a; simp [*, sum.swap]⟩

def sum.merge {α : Type u} {X : set α} :
    {a // a ∈ X} ⊕ {a // a ∉ X} → α
| (sum.inl ⟨a, _⟩) := a
| (sum.inr ⟨a, _⟩) := a

def equinumerous.disjoint_union {α : Type u} {X : set α} [∀ a, decidable $ a ∈ X] :
    α ≅ ({a // a ∈ X} ⊕ {a // a ∉ X}) :=
⟨λ a, if h : a ∈ X then sum.inl ⟨a,h⟩ else sum.inr ⟨a,h⟩, sum.merge,
begin
    intro b,
    by_cases sum.merge b ∈ X; simp [*];
    cases b; cases a with b bx; simp [sum.merge] at h;
    try {contradiction}; refl
end,
begin intro a, by_cases a ∈ X; simp [sum.merge, *], end⟩

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

def part1 (ginj: injective g) : {b // b ∈ -(f '' -X)} ≅ {a // a ∈ X} :=
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

def part2 (finj: injective f) : {a // a ∈ -X} ≅ {b // b ∈ f '' -X} :=
⟨h2, h2_inj finj, h2_surj⟩

noncomputable lemma eqn (finj : injective f) (ginj : injective g) : α ≅ β :=
calc α ≅ ({a // a ∈ X} ⊕ {a // a ∉ X}) : equinumerous.disjoint_union
   ... ≅ ({b // b ∈ -(f '' -X)} ⊕ {b // b ∈ f '' -X}) :
            equinumerous.congr_sum (part1 ginj).symm (part2 finj)
   ... ≅ ({b // b ∈ f '' -X} ⊕ {b // b ∈ -(f '' -X)}) : equinumerous.sum_comm
   ... ≅ β : equinumerous.disjoint_union.symm

end
end set.cantor_schroeder_bernstein

namespace set
variables {α β γ : Type u}

noncomputable def cantor_schroeder_bernstein : α ≼ β → β ≼ α → α ≅ β
| ⟨f, finj⟩ ⟨g, ginj⟩ := set.cantor_schroeder_bernstein.eqn _ _ finj ginj

end set
