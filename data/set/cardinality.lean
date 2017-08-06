import data.set.basic
import algebra.lattice.fixed_points
import data.set.lattice
import data.set.classical_inverse
import algebra.lattice.zorn
import data.set.function
universes u v w

namespace function

variables {α : Type u} {β : Type v} {f : α → β} (fbij : bijective f)

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

lemma ulift.down.inj (α : Type u) : injective (@ulift.down α)
| x y h := by cases x; cases y; cases h; refl

def set.dominated_by (α : Type u) (β : Type v) : Prop :=
∃ f : α → β, injective f

local infix ` ≼ `:50 := set.dominated_by

def set.equinumerous (α : Type u) (β : Type v) : Prop :=
∃ f : α → β, bijective f

local infix ` ≅ `:50 := set.equinumerous

namespace set
variables {α : Type u} {β : Type v} {γ : Type w}

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

@[congr]
lemma equinumerous.congr_eqn {α α' β β'} :
    α ≅ α' → β ≅ β' → (α ≅ β) = (α' ≅ β') :=
begin
intros ha hb, apply propext, split; intro h,
{transitivity, apply equinumerous.symm, apply ha, transitivity, apply h, apply hb},
{transitivity, apply ha, transitivity, apply h, apply equinumerous.symm, apply hb},
end

def sum.map {α α' β β'} (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr (g b)

@[congr]
lemma dominated.congr_sum {α α' β β'} : α ≼ α' → β ≼ β' → (α ⊕ β) ≼ (α' ⊕ β')
| ⟨f, finj⟩ ⟨g, ginj⟩ := ⟨sum.map f g, begin
intros a b, cases a; cases b; simp [sum.map]; intro h; injection h; tactic.congr,
apply finj, assumption, apply ginj, assumption
end⟩

@[congr]
lemma equinumerous.congr_sum {α α' β β'} :
    α ≅ α' → β ≅ β' → (α ⊕ β) ≅ (α' ⊕ β')
| ⟨f, fbij⟩ ⟨g, gbij⟩ :=
⟨sum.map f g, begin
intros a b, cases a; cases b; simp [sum.map]; intro h; injection h; tactic.congr,
apply fbij.left, assumption, apply gbij.left, assumption
end, begin
intro c, cases c with a b,
{cases fbij.right a with a aspec, existsi sum.inl a, simp [sum.map, *] },
{cases gbij.right b with b bspec, existsi sum.inr b, simp [sum.map, *] }
end⟩

@[simp] lemma sum_ulift {α : Type v} : ulift α ≅ α :=
⟨ulift.down,
begin intros x y h, cases x; cases y; simp [sum.map, *] at * end,
begin intro b, existsi ulift.up b, refl end⟩

@[simp]
lemma sum_empty {α : Type u} : (α ⊕ empty) ≅ α :=
equinumerous.symm ⟨sum.inl, @sum.inl.inj _ _,
    begin intro b, cases b, existsi a, refl, cases a end⟩

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

def sum.reassoc {α β γ} : ((α ⊕ β) ⊕ γ) → (α ⊕ (β ⊕ γ))
| (sum.inl (sum.inl a)) := sum.inl a
| (sum.inl (sum.inr b)) := sum.inr (sum.inl b)
| (sum.inr c) := sum.inr (sum.inr c)

lemma equinumerous.sum_assoc {α β γ} : ((α ⊕ β) ⊕ γ) ≅ (α ⊕ (β ⊕ γ)) :=
⟨sum.reassoc,
begin intros a b h, cases a; cases a <|> skip; cases b; cases a_1 <|> skip;
    simp [sum.reassoc] at h; cc end,
begin intro b, cases b, exact ⟨sum.inl (sum.inl a), rfl⟩,
    cases a, exact ⟨sum.inl (sum.inr a), rfl⟩, exact ⟨sum.inr a, rfl⟩ end⟩

@[congr]
lemma equinumerous.congr_prod {α α' β β'} :
    α ≅ α' → β ≅ β' → (α × β) ≅ (α' × β')
| ⟨f, finj, fsurj⟩ ⟨g, ginj, gsurj⟩ :=
⟨λ ⟨x, y⟩, ⟨f x, g y⟩,
λ ⟨xa, ya⟩ ⟨xb, yb⟩, begin simp, intro h, cases h with hx hy, split,
    {apply finj, assumption}, {apply ginj, assumption} end,
λ ⟨x, y⟩, begin simp,
    cases fsurj x with x', existsi x', simp *,
    cases gsurj y with y', existsi y', simp *,
end⟩

lemma equinumerous.prod_comm {α : Type u} {β : Type v} :
    (α × β) ≅ (β × α) :=
⟨λ ⟨x, y⟩, ⟨y, x⟩,
λ ⟨xa, ya⟩ ⟨xb, yb⟩, by simp; intro h; cases h with hx hy; split; assumption,
λ ⟨y, x⟩, ⟨⟨x, y⟩, rfl⟩⟩

lemma equinumerous.prod_assoc {α : Type u} {β : Type v} {γ : Type w} :
    ((α × β) × γ) ≅ (α × (β × γ)) :=
⟨λ ⟨⟨x, y⟩, z⟩, ⟨x, y, z⟩,
λ ⟨⟨xa,ya⟩, za⟩ ⟨⟨xb, yb⟩, zb⟩, by simp; intro h; simp *,
λ ⟨x, y, z⟩, ⟨⟨⟨x,y⟩, z⟩, rfl⟩⟩

@[simp]
lemma equinumerous.prod_unit {α : Type u} : (α × unit) ≅ α :=
⟨prod.fst, λ a b, by cases a; cases b; cc, λ a, ⟨(a, ()), rfl⟩⟩

@[simp]
lemma equinumerous.prod_empty {α : Type u} : (α × empty) ≅ empty :=
equinumerous.symm ⟨empty.rec _, λ a b, match b with end, λ a, match a with end⟩

lemma prod_sum_distrib {α β γ} : (α × (β ⊕ γ)) ≅ ((α × β) ⊕ (α × γ)) :=
⟨λ ⟨a, bc⟩, match bc with
    | sum.inl b := sum.inl (a, b)
    | sum.inr c := sum.inr (a, c)
    end,
λ ⟨xa, xbc⟩ ⟨ya, ybc⟩, begin
clear _fun_match, clear _fun_match,
simp at *, cases xbc with xb xc; cases ybc with yb yc; simp; cc,
end,
begin intro abc, cases abc with ab ac; cases ab with a b <|> cases ac with a c; simp; existsi a,
{existsi sum.inl b, simp}, {existsi sum.inr c, simp}, end⟩

local attribute [instance] classical.prop_decidable
lemma equinumerous.disjoint_union {α : Type u} {X : set α} :
    α ≅ ({a // a ∈ X} ⊕ {a // a ∉ X}) :=
⟨λ a, if h : a ∈ X then sum.inl ⟨a,h⟩ else sum.inr ⟨a,h⟩,
begin
    intros a b,
    by_cases a ∈ X with ax; by_cases b ∈ X with bx;
    simp*; intro h; repeat {injection h},
end,
by intros a; cases a with a a; cases a with a ax; existsi a; simp*⟩

end set

namespace set.cantor_schroeder_bernstein
section
open set
parameters {α β : Type u} (f : α → β) (g : β → α)

def phi (x : set α) : set α :=
g '' -(f '' -x)

lemma phi_monotone : monotone phi
| x y xiny := begin
apply image_subset, apply compl_subset,
apply image_subset, apply compl_subset,
assumption
end

def X := lattice.lfp phi

lemma X_spec : X = g '' -(f '' -X) :=
show X = phi X, by unfold X; rw [←lattice.lfp_eq (phi_monotone f g)]

def h1inv : {b // b ∈ -(f '' -X)} → {a // a ∈ X} | ⟨b, bnfnx⟩ :=
⟨g b, begin rw X_spec, apply mem_image bnfnx rfl end⟩

lemma h1inv_inj (ginj : injective g) : injective h1inv
| ⟨a, anfnx⟩ ⟨b, bnfnx⟩ gaeqgb :=
begin injection gaeqgb, tactic.congr, apply ginj, assumption end

lemma h1inv_surj : surjective h1inv
| ⟨a, ax⟩ := begin
rw X_spec at ax, cases ax with b bspec,
refine ⟨⟨b, bspec.left⟩, _⟩,
unfold h1inv, tactic.congr, apply bspec.right
end

lemma part1 (ginj: injective g) : {b // b ∈ -(f '' -X)} ≅ {a // a ∈ X} :=
⟨h1inv, h1inv_inj ginj, h1inv_surj⟩

def h2 : {a // a ∈ -X} → {b // b ∈ f '' -X} | ⟨a, hnx⟩ :=
⟨f a, mem_image hnx rfl⟩

lemma h2_inj (finj : injective f) : injective h2
| ⟨a, anx⟩ ⟨b, bnx⟩ faeqfb :=
begin tactic.congr, injection faeqfb, apply finj, assumption end

lemma h2_surj : surjective h2
| ⟨b, ⟨a, aspec⟩⟩ := ⟨⟨a, aspec.left⟩, by { unfold h2, tactic.congr, apply aspec.right }⟩

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
open set.graph

structure pif (α β : Type u) :=
(g : α → β → Prop)
(pfn : partial_fun g)
(inj : set.graph.injective g)

instance (α β : Type u) : partial_order (pif α β) := {
    le := λ f g, f.g ≤ g.g,
    le_refl := λ f, le_refl _,
    le_trans := λ f g h fg gh, le_trans fg gh,
    le_antisymm := begin intros f g fg gf, cases f, cases g,
        tactic.congr, apply le_antisymm; assumption end
}

lemma ex_max (α β : Type u) : ∃ m : pif α β, ∀ a ≥ m, a = m :=
zorn.zorn_partial_order
begin
intros c hc,
let g : α → β → Prop := λ a b, ∃ p ∈ c, pif.g p a b,
have gpfn : partial_fun g, {
    intros a b1 b2 hb1 hb2,
    cases hb1 with p1 hp1, cases hp1 with hp1 hg1,
    cases hb2 with p2 hp2, cases hp2 with hp2 hg2,
    cases hc p1 hp1 p2 hp2 with hle hle,
    {apply p2.pfn, apply hle, assumption, assumption},
    {apply p1.pfn, assumption, apply hle, assumption}
},
have ginj : set.graph.injective g, {
    intros a1 a2 b b2 hab1 hab2 hbeq, cases hbeq, clear hbeq,
    cases hab1 with p1 hp1, cases hp1 with hp1 hg1,
    cases hab2 with p2 hp2, cases hp2 with hp2 hg2,
    cases hc p1 hp1 p2 hp2 with hle hle,
    {apply p2.inj, apply hle, assumption, assumption, refl},
    {apply p1.inj, assumption, apply hle, assumption, refl}
},
let ub : pif α β := ⟨g, gpfn, ginj⟩,
refine ⟨ub, _⟩,
intros p hp a b hpab,
exact ⟨p, hp, hpab⟩,
end

local attribute [instance] classical.prop_decidable

lemma comp (α β : Type u) : α ≼ β ∨ β ≼ α :=
let ⟨m, hm⟩ := ex_max α β in
let minv := λ b a, m.g a b in
if htot : set.graph.total m.g then
    or.inl ⟨λ a, set.graph.apply m.g a (htot _), begin
        intros a1 a2 heq,
        apply m.inj,
        {apply apply_spec, apply htot},
        {apply apply_spec, apply htot},
        simp * at *,
    end⟩
else
    have hinvtot: set.graph.total minv, begin
        cases exists_not_of_not_forall htot with a ha, simp at ha,
        intro b, by_contra hb,
        let g' := λ a' b', m.g a' b' ∨ (a' = a ∧ b' = b),
        have g'pfn : set.graph.partial_fun g', {
            intros a1 b1 b2 h1 h2,
            revert g', by_cases a1 = a; simp [h],
            {have: ∀ b, ¬m.g a b, {intros b h, apply ha, existsi b, assumption}, simp [*], cc},
            {intros, apply m.pfn, assumption, assumption},
        },
        have g'inj : set.graph.injective g', {
            intros a1 a2 b1 b2 h1 h2 heq, cases heq, clear heq,
            revert g', by_cases b1 = b; simp [h],
            {have: ∀ a, ¬m.g a b, {intros a h, apply hb, existsi a, assumption}, simp [*], cc},
            {intros, apply m.inj, assumption, assumption, refl},
        },
        let m' : pif α β := ⟨g', g'pfn, g'inj⟩,
        have: m ≤ m', {intros a' b', revert g', simp, intros g'pfn g'inj, simp, intro h, simp [h] },
        have hmm' : m' = m := hm m' this,
        have: a ∈ dom m'.g, {existsi b, revert g', simp, intros, simp},
        have: a ∉ dom m'.g, {rw hmm', assumption},
        contradiction
    end,
    or.inr ⟨λ a, set.graph.apply minv a (hinvtot _), begin
        intros a1 a2 heq, simp at heq,
        apply m.pfn,
        {change minv a1 _, apply apply_spec, apply hinvtot},
        {rw heq, change minv a2 _, apply apply_spec},
    end⟩

end set.comparable

namespace set

@[instance] def equinumerosity_setoid : setoid (Type u) :=
{ r := (≅),
  iseqv := ⟨@equinumerous.refl, @equinumerous.symm, @equinumerous.trans⟩ }

@[simp] lemma equinumerous_of_setoid (α β : Type u) : (α ≈ β) = (α ≅ β) :=
rfl

def cardinality : Type (u+1) :=
quotient equinumerosity_setoid

@[reducible] def card_core (α : Type u) : cardinality.{u} := ⟦α⟧
local prefix `#`:100 := card_core
def card (α : Type v) : cardinality.{max v u} := # ulift α

namespace cardinality

protected def le (a b : cardinality) : Prop :=
quotient.lift_on₂ a b (≼) begin
    intros; apply propext; split; apply dominated_eqn_congr;
    try { assumption <|> `[apply equinumerous.symm; assumption] }
end

instance : linear_order cardinality.{u} := {
    le := cardinality.le,
    le_refl := begin
        refine quotient.ind _, intro a,
        apply dominated_by_refl
    end,
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
    le_total := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        apply set.comparable.comp
    end,
}

def aleph0 : cardinality.{u} := card ℕ

instance: has_zero cardinality.{u} := ⟨card empty⟩
instance: has_one cardinality.{u} := ⟨card unit⟩

lemma zero_card_empty : 0 = card empty := rfl
lemma one_card_unit : 1 = card unit := rfl

lemma le_iff_dom (α β : Type u) : #α ≤ #β ↔ α ≼ β :=
iff.refl _

lemma lt_iff_not_dom (α β : Type u) : #α < #β ↔ ¬ β ≼ α :=
by simp [lt_iff_not_ge, ge, le_iff_dom]

lemma eq_iff_equinumerous (α β : Type u) : #α = #β ↔ α ≅ β :=
begin
simp [le_antisymm_iff], split; intro h,
{cases h, apply cantor_schroeder_bernstein; apply (le_iff_dom _ _).mp; assumption, },
{split; apply (le_iff_dom _ _).mpr; apply equinumerous.dominates, assumption, apply equinumerous.symm; assumption}
end

lemma eq_of_equinumerous (α β : Type u) : α ≅ β → #α = #β :=
(eq_iff_equinumerous _ _).mpr

lemma lt_of_not_dom {α β : Type u} : ¬ β ≼ α → #α < #β :=
(lt_iff_not_dom _ _).mpr

protected lemma zero_lt_one : 0 < (1 : cardinality) :=
lt_of_not_dom (λ ⟨f, _⟩, empty.rec _ (f (ulift.up ())).down)

@[elab_as_eliminator]
protected lemma ind {β : cardinality.{u} → Prop} : (∀ a, β #a) → ∀ c, β c :=
quotient.ind

protected def add (a b : cardinality.{u}) : cardinality.{u} :=
quotient.lift_on₂ a b (λ a b, card.{u u} (a ⊕ b)) begin
simp, intros, apply eq_of_equinumerous, simp,
apply equinumerous.congr_sum; assumption,
end
instance: has_add cardinality.{u} := ⟨cardinality.add⟩

protected lemma add_zero (a : cardinality.{u}) : a + 0 = a :=
begin
revert a, refine cardinality.ind _, intro a,
apply eq_of_equinumerous, simp,
end

protected lemma add_assoc (a b c : cardinality.{u}) : (a + b) + c = a + (b + c) :=
begin
revert a b c,
refine cardinality.ind _, intro a,
refine cardinality.ind _, intro b,
refine cardinality.ind _, intro c,
apply eq_of_equinumerous, simp, apply equinumerous.sum_assoc
end

protected lemma add_comm (a b : cardinality.{u}) : a + b = b + a :=
begin
revert a b,
refine cardinality.ind _, intro a,
refine cardinality.ind _, intro b,
apply eq_of_equinumerous, simp,
apply equinumerous.sum_comm
end

protected def mul (a b : cardinality.{u}) : cardinality.{u} :=
quotient.lift_on₂ a b (λ a b, card.{u u} (a × b)) begin
simp, intros, apply eq_of_equinumerous, simp, apply equinumerous.congr_prod; assumption,
end
instance: has_mul cardinality.{u} := ⟨cardinality.mul⟩

lemma mul_card (a b) : card a * card b = card (a × b) :=
by apply eq_of_equinumerous; simp

protected lemma mul_zero (a : cardinality.{u}) : a * 0 = 0 :=
begin
revert a, refine cardinality.ind _, intro a,
simp [zero_card_empty],
apply eq_of_equinumerous, simp
end

protected lemma mul_one (a : cardinality.{u}) : a * 1 = a :=
begin
revert a, refine cardinality.ind _, intro a,
apply eq_of_equinumerous, simp
end

protected lemma mul_comm (a b : cardinality.{u}) : a * b = b * a :=
begin
revert a b,
refine cardinality.ind _, intro a,
refine cardinality.ind _, intro b,
apply eq_of_equinumerous, simp, apply equinumerous.prod_comm
end

protected lemma mul_assoc (a b c : cardinality.{u}) : (a * b) * c = a * (b * c) :=
begin
revert a b c,
refine cardinality.ind _, intro a,
refine cardinality.ind _, intro b,
refine cardinality.ind _, intro c,
apply eq_of_equinumerous, simp, apply equinumerous.prod_assoc
end

protected lemma left_distrib (a b c : cardinality.{u}) : a * (b + c) = a * b + a * c :=
begin
revert a b c,
refine cardinality.ind _, intro a,
refine cardinality.ind _, intro b,
refine cardinality.ind _, intro c,
apply eq_of_equinumerous, simp, apply prod_sum_distrib
end

instance: comm_semiring cardinality.{u} := {
    zero := 0,
    add := (+),
    add_assoc := cardinality.add_assoc,
    add_comm := cardinality.add_comm,
    add_zero := cardinality.add_zero,
    zero_add := by intro; rw [cardinality.add_comm, cardinality.add_zero],

    one := 1,
    mul := (*),
    mul_one := cardinality.mul_one,
    one_mul := by intro; rw [cardinality.mul_comm, cardinality.mul_one],
    mul_assoc := cardinality.mul_assoc,
    mul_comm := cardinality.mul_comm,
    mul_zero := cardinality.mul_zero,
    zero_mul := by intro; rw [cardinality.mul_comm, cardinality.mul_zero],

    left_distrib := cardinality.left_distrib,
    right_distrib := by intros; simp [cardinality.mul_comm, cardinality.left_distrib],
}

end cardinality

end set