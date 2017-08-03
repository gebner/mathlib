import algebra.order

universes u v

inductive pempty : Sort u.

instance : subsingleton pempty := ⟨by intros a b; cases a; cases b; refl⟩
instance : subsingleton empty := ⟨by intros a b; cases a; cases b; refl⟩
instance : subsingleton punit := ⟨by intros a b; cases a; cases b; refl⟩

lemma ulift.down.inj {α : Type u} : function.injective (@ulift.down.{v u} α) :=
begin intros x y hxy, cases x, cases y, simp * at * end

lemma well_founded.irrefl {α : Type u} {r : α → α → Prop} (hwf : well_founded r) : ∀ a, ¬r a a :=
well_founded.fix hwf (λ a ih raa, ih a raa raa)

class well_order (α : Type u) extends linear_order α :=
(wf : well_founded ((<) : α → α → Prop))

namespace well_order

instance (α) [well_order α] : has_well_founded α :=
{ r := (<), wf := well_order.wf _ }

protected def le (α : Type u) (β : Type v) [well_order α] [well_order β] :=
∃ f : α → β, strictly_monotone f

section
local infix ` ≤ ` := well_order.le

@[refl]
protected lemma le_refl (α) [well_order α] : α ≤ α :=
⟨id, by intros x y hxy; assumption⟩

@[trans]
protected lemma le_trans {α β γ} [well_order α] [well_order β] [well_order γ] :
    α ≤ β → β ≤ γ → α ≤ γ
| ⟨f, hf⟩ ⟨g, hg⟩ := ⟨g ∘ f, by intros x y hx; apply hg; apply hf; assumption⟩
end

open function

def preorder_preimage {α β} [preorder β] (f : α → β) : preorder α := {
    le := λ a b : α, f a ≤ f b,
    lt := λ a b : α, f a < f b,
    le_refl := λ _, le_refl _,
    le_trans := λ a b c hab hbc, le_trans hab hbc,
    lt_iff_le_not_le := by intros a b; simp [lt_iff_le_not_le],
}

def partial_order_preimage {α β} [partial_order β] (f : α → β)
        (finj : injective f) : partial_order α := {
    preorder_preimage f with
    le_antisymm := λ a b hab hbc, finj (le_antisymm hab hbc),
}

def linear_order_preimage {α β} [linear_order β] (f : α → β)
        (finj : injective f) : linear_order α := {
    partial_order_preimage f finj with
    le_total := λ a b, le_total _ _,
}

lemma well_founded_preimage {α β} (r : β → β → Prop)
    (hwf : well_founded r) (f : α → β) : well_founded (λ a b, r (f a) (f b)) :=
begin
constructor, intros x,
have: acc r (f x) → acc (λ a b, r (f a) (f b)) x, {
    generalize hfx : f x = fx,
    intros hacc, induction hacc with x hacc ih generalizing x hfx,
    subst hfx,
    constructor, intros y hr,
    apply ih, apply hr, refl
},
intros, apply this, apply well_founded.apply hwf
end

def well_order_preimage {α : Type u} {β : Type v} [wo : well_order β] (f : α → β)
        (finj : injective f) : well_order α := {
    linear_order_preimage f finj with
    wf := well_founded_preimage _ wo.wf _,
}

instance nat : well_order ℕ :=
{ nat.linear_order with wf := nat.lt_wf }

instance fin (n) : well_order (fin n) :=
well_order.well_order_preimage fin.val (@fin.eq_of_veq _)

instance ulift (α) [well_order α] : well_order (ulift.{v u} α) :=
well_order.well_order_preimage ulift.down ulift.down.inj

instance subsingleton (α) [h : subsingleton α] : well_order α := {
    le := λ a b, true,
    le_refl := by intros; trivial,
    le_trans := by intros; trivial,
    le_antisymm := by intros; apply subsingleton.elim,
    le_total := begin
        intros a b, have: a = b, apply subsingleton.elim,
        subst this, apply or.inl, apply le_refl
    end,
    wf := begin
        constructor, intro a, constructor, intros b hba,
        have: a = b, apply subsingleton.elim, subst this,
        cases hba, contradiction
    end
}

protected def sum.le {α β} [preorder α] [preorder β] : α ⊕ β → α ⊕ β → Prop
| (sum.inl a1) (sum.inl a2) := a1 ≤ a2
| (sum.inl _) (sum.inr _) := true
| (sum.inr _) (sum.inl _) := false
| (sum.inr b1) (sum.inr b2) := b1 ≤ b2

protected def sum.lt {α β} [preorder α] [preorder β] : α ⊕ β → α ⊕ β → Prop
| (sum.inl a1) (sum.inl a2) := a1 < a2
| (sum.inl _) (sum.inr _) := true
| (sum.inr _) (sum.inl _) := false
| (sum.inr b1) (sum.inr b2) := b1 < b2

protected lemma sum.lt_iff_le_not_le {α β} [preorder α] [preorder β] (a b : α ⊕ β) :
    sum.lt a b ↔ (sum.le a b ∧ ¬ sum.le b a) :=
by cases a; cases b; simp [sum.lt, sum.le, lt_iff_le_not_le]

private lemma sum.lt_wf {α β} [woa : well_order α] [wob : well_order β] : @well_founded (α ⊕ β) sum.lt :=
begin
have accl: ∀ a : α, @acc (α ⊕ β) sum.lt (sum.inl a), {
    intro a,
    have h: acc (<) a, {apply well_founded.apply woa.wf},
    induction h, constructor, intros y hy,
    cases y, apply ih_1, apply hy, cases hy,
},
have accr: ∀ b : β, @acc (α ⊕ β) sum.lt (sum.inr b), {
    intro b,
    have h: acc (<) b, {apply well_founded.apply wob.wf},
    induction h, constructor, intros y hy,
    cases y, apply accl, apply ih_1, apply hy,
},
constructor, intro a, cases a, apply accl, apply accr
end

instance sum (α β) [woa : well_order α] [wob : well_order β] : well_order (α ⊕ β) := {
    le := sum.le, lt := sum.lt,
    lt_iff_le_not_le := sum.lt_iff_le_not_le,
    le_refl := by intro a; cases a; simp [sum.le],
    le_trans := by intros a b c; cases a; cases b; cases c;
        simp [sum.le]; intros hab hbc; transitivity; assumption,
    le_antisymm := show ∀ a b, sum.le a b → sum.le b a → a = b,
        by intros a b; cases a; cases b; simp [sum.le];
            intros; apply congr_arg; apply le_antisymm; assumption,
    le_total := show ∀ a b, sum.le a b ∨ sum.le b a,
        by intros a b; cases a; cases b; simp [sum.le]; apply le_total,
    wf := sum.lt_wf,
}

lemma inv_of_equiv (α β) [well_order α] [wob : well_order β] (f : α → β) (g : β → α) :
    strictly_monotone f → strictly_monotone g → ∀ b, f (g b) = b
| fmon gmon b :=
@well_founded.induction _ _ wob.wf (λ b, f (g b) = b) b begin
intros x ih,
end






end well_order

structure pre_ord :=
(carrier : Type u) (wo : well_order carrier)

attribute [instance] pre_ord.wo

namespace pre_ord

instance : preorder pre_ord := {
    le := λ a b, well_order.le a.carrier b.carrier,
    le_refl := λ _, well_order.le_refl _,
    le_trans := λ _ _ _, well_order.le_trans,
}

instance : setoid pre_ord :=
preorder.setoid

lemma le_total (a b : pre_ord) : a ≤ b ∨ b ≤ a :=
begin
end

protected def add : pre_ord.{u} → pre_ord.{u} → pre_ord.{u}
| ⟨α, wo1⟩ ⟨β, wo2⟩ := ⟨α ⊕ β, by apply_instance⟩

lemma bij_of_equiv (a b : pre_ord.{u}) :
    a ≈ b → ∃ f : a.carrier → b.carrier, strictly_monotone f ∧ function.bijective f
| ⟨⟨fab, hab⟩, ⟨fba, hba⟩⟩ :=
begin
existsi fab, split, apply hab,
split, apply injective_of_strictly_monotone; assumption,
intro a, existsi fba a,
end







end pre_ord

def ord := quotient pre_ord.setoid

namespace ord

protected def le (a b : ord.{u}) : Prop :=
quotient.lift_on₂ a b (≤)
begin
intros a1 a2 b1 b2 hab1 hab2,
apply propext,
apply preorder.equiv_congr_le; assumption
end

instance : linear_order ord.{u} := {
    le := ord.le,
    le_refl := quotient.ind begin intro a, apply le_refl end,
    le_trans := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        refine quotient.ind _, intro c,
        apply le_trans,
    end,
    le_antisymm := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        intros hab hba,
        apply quotient.sound,
        exact ⟨hab, hba⟩
    end,
    le_total := begin
        refine quotient.ind _, intro a,
        refine quotient.ind _, intro b,
        apply pre_ord.le_total
    end,
}

protected def mk (α : Type u) [well_order α] : ord.{max u v} :=
quotient.mk ⟨ulift α, by apply_instance⟩

protected def zero : ord.{u} := ord.mk empty
instance: has_zero ord.{u} := ⟨ord.zero⟩

protected def one : ord.{u} := ord.mk unit
instance: has_one ord.{u} := ⟨ord.one⟩

protected def add (a b : ord.{u}) : ord.{u} :=
quotient.lift_on₂ a b (λ a b, quotient.mk (pre_ord.add a b))
begin
intros a1 a2 b1 b2 hab1 hab2, apply quot.sound,
cases hab1 with f1 h1,
end

lemma zero_le (x : ord.{u}) : 0 ≤ x :=
quotient.induction_on x begin
intro x, cases x with x hx,
refine ⟨λ x, match x with end, _⟩,
intro, cases a, cases down
end

-- protected def of_nat (n : ℕ) : ord.{u} :=
-- ord.mk (fin n)

-- instance : has_coe ℕ ord.{u} := ⟨ord.of_nat⟩

-- protected def zero : ord.{u} := (0 : ℕ)
-- instance : has_zero ord.{u} := ⟨ord.zero⟩

-- private lemma nat_le_of_mon (m n : ℕ) (f : ulift.{u 0} (fin m) → ulift.{u 0} (fin n))
--     (fmon : strictly_monotone f) : m ≤ n :=
-- begin
-- have finj := injective_of_strictly_monotone fmon,
-- let g : fin m → fin n := λ i, ulift.down (f (ulift.up i)),
-- have ginj : function.injective g, {
--     intros i j hij,
--     have := ulift.down.inj hij,
--     have := finj this,
--     have := ulift.up.inj this,
--     assumption
-- },

-- end

-- lemma of_nat_inj : function.injective ord.of_nat :=
-- begin
-- intros x y hxy,
-- have hxy := quotient.exact hxy,
-- cases hxy with hxy hyx, cases hxy with fxy hfxy, cases hyx with fyx hfyx,
-- end

end ord