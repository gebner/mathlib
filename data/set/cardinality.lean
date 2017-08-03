import data.set.basic
import algebra.lattice.fixed_points
import data.set.lattice
import data.set.classical_inverse
import algebra.lattice.zorn
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

namespace set.comparable
section
variables {α β : Type u}

structure pif (α β : Type u) :=
(d : set α)
(f : subtype d → β)
(finj : injective f)

local attribute [instance] classical.prop_decidable
def pif.le : pif α β → pif α β → Prop
| ⟨d1, f1, _⟩ ⟨d2, f2, _⟩ :=
    if h : d1 ⊆ d2 then
        ∀ x ∈ d1, f1 ⟨x, H⟩ = f2 ⟨x, by exact h H⟩
    else false
local attribute [simp] pif.le

instance: partial_order (pif α β) := {
    le := pif.le,
    le_refl := show ∀ a, pif.le a a,
        begin intro a, cases a with d f finj a,
            have: d ⊆ d, {reflexivity},
            simp [pif.le, *], cc
        end,
    le_trans := show ∀ a b c : pif α β, pif.le a b → pif.le b c → pif.le a c,
        begin intros a b c hab hbc,
            cases a with d1 f1 finj1,
            cases b with d2 f2 finj2,
            cases c with d3 f3 finj3,
            by_cases d1 ⊆ d2; by_cases d2 ⊆ d3; simp * at *,
            have: d1 ⊆ d3, {transitivity; assumption},
            simp *, intros, simp *
        end,
    le_antisymm := show ∀ a b : pif α β, pif.le a b → pif.le b a → a = b,
        begin intros a b hab hba,
            cases a with d1 f1 finj1,
            cases b with d2 f2 finj2,
            by_cases d1 ⊆ d2; by_cases d2 ⊆ d1; simp * at *,
            clear hab,
            have: d1 = d2, {apply set.subset.antisymm; assumption}, subst this,
            have: f1 = f2, {apply funext, intros, cases x, simp *, tactic.congr}, subst this
        end
}

#print "foo"


set_option pp.proofs true
-- set_option pp.all true
lemma ex_max : ∃ m : pif α β, ∀ a, a ≥ m → a = m :=
zorn.zorn_partial_order
begin
intros c hc,
let d := λ a : α, ∃ p : pif α β, p ∈ c ∧ a ∈ p.d,
let f : subtype d → β := λ ⟨a, ha⟩,
    (classical.some ha).f ⟨a, (classical.some_spec ha).right⟩,
have finj: injective f, {intros a b heq,
    cases a with a ha, cases b with b hb,
    revert f, simp,
    generalize: (classical.some_spec ha).right = had,
    generalize: (classical.some_spec hb).right = hbd,
    revert had hbd,
    generalize hsa: classical.some ha = sa,
    generalize hsb: classical.some hb = sb,
    have hcab := hc sa _ sb _,
    {cases sa with da fa fainj, cases sb with db fb fbinj,
    dsimp, intros had hbd heq,
    simp [has_le.le, preorder.le, partial_order.le] at hcab,
    cases hcab with hcab hcab,
    { by_cases da ⊆ db; simp [h] at hcab; try {contradiction},
      have: (⟨a, h had⟩ : subtype db) = ⟨b, hbd⟩,
      apply fbinj, transitivity,
      apply (hcab _ _).symm; assumption, assumption,
      injection this, cc,
    },
    { by_cases db ⊆ da; simp [h] at hcab; try {contradiction},
      have: (⟨a, had⟩ : subtype da) = ⟨b, h hbd⟩,
      apply fainj, transitivity, assumption,
      apply (hcab _ _); assumption,
      injection this, cc,
    }},
    {rw ← hsa, apply (classical.some_spec ha).left},
    {rw ← hsb, apply (classical.some_spec hb).left},
},
refine ⟨⟨d, f, finj⟩, _⟩,
intro a, have hc := hc a, cases a with da fa fainj, intro hac,
have hdad: da ⊆ d, {intros a hda, refine ⟨_, hac, hda⟩},
simp [hdad, has_le.le, preorder.le, partial_order.le],
intros a hda,
revert f, simp, intros finj,
generalize: ((iff_true_intro hdad).mpr true.intro hda) = had,
cases classical.some_spec had with hadc,
cases hc hac (classical.some had) hadc,
{cases classical.some had,
 by_cases da ⊆ d_1; simp [h, has_le.le, preorder.le, partial_order.le, pif.le] at a_2,
 apply a_2, cases a_2},
{cases classical.some had,
 by_cases d_1 ⊆ da; simp [h, has_le.le, preorder.le, partial_order.le, pif.le] at a_2,
 apply a_2, cases a_2},
end




#check zorn.zorn_partial_order

end
end set.comparable

namespace set

@[instance] def equinumerosity_setoid : setoid (Type u) :=
{ r := (≅),
  iseqv := ⟨@equinumerous.refl, @equinumerous.symm, @equinumerous.trans⟩ }

def cardinality : Type (u+1) :=
quotient equinumerosity_setoid

def card (α : Type u) : cardinality := ⟦α⟧

namespace cardinality

protected def le (a b : cardinality) : Prop :=
quotient.lift_on₂ a b (≼) begin
    intros; apply propext; split; apply dominated_eqn_congr;
    try { assumption <|> `[apply equinumerous.symm; assumption] }
end

protected def has_le : has_le cardinality := ⟨cardinality.le⟩
local attribute [instance] cardinality.has_le

instance : linear_order cardinality.{u} := {
    le := cardinality.le,
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
    le_total := _,
}

end cardinality

end set