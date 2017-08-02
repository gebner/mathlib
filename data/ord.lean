import algebra.order

universes u v

lemma well_founded.irrefl {α : Type u} {r : α → α → Prop} (hwf : well_founded r) : ∀ a, ¬r a a :=
well_founded.fix hwf (λ a ih raa, ih a raa raa)

class well_order (α : Type u) extends linear_strong_order_pair α :=
(wf : well_founded lt)

namespace well_order

instance (α) [well_order α] : has_well_founded α :=
{ r := (<), wf := well_order.wf _ }

protected def le (α : Type u) (β : Type v) [well_order α] [well_order β] :=
∃ f : α → β, monotone f

local infix ` ≤ ` := well_order.le

@[refl]
protected lemma le_refl (α) [well_order α] : α ≤ α :=
⟨id, by intros x y hxy; assumption⟩

@[trans]
protected lemma le_trans {α β γ} [well_order α] [well_order β] [well_order γ] :
    α ≤ β → β ≤ γ → α ≤ γ
| ⟨f, hf⟩ ⟨g, hg⟩ := ⟨g ∘ f, by intros x y hx; apply hg; apply hf; assumption⟩

section
local attribute [instance] classical.prop_decidable
protected def preimage {α β} {f : α → β} [wo : well_order β] (finj : function.injective f) :
        well_order α :=
have wf : well_founded (λ a b, f a < f b), begin

end, {
    lt := λ a b, f a < f b,
    wf := wf,
    lt_irrefl := begin apply well_founded.irrefl wf end,

    le := λ a b, f a < f b ∨ a = b,
    le_iff_lt_or_eq := λ a b, iff.refl _,
    le_refl := λ a, or.inr rfl,
    le_trans := begin
        intros a b c altb altc,
        cases altb; cases altc,
        { left, transitivity; assumption },
        { left, subst a_2, assumption },
        { left, subst a_1, assumption },
        { right, subst a_1, assumption },
    end,
    le_antisymm := _,
    le_total := _,
}
end

end well_order

structure pre_ord :=
(carrier : Type u) (wo : well_order carrier)

attribute [instance] pre_ord.wo

namespace pre_ord

protected def le (a b : pre_ord) :=
well_order.le a.carrier b.carrier

local infix ` ≤ ` := pre_ord.le

@[refl]
protected lemma le_refl (a) : a ≤ a :=
well_order.le_refl _

@[trans]
protected lemma le_trans {a b c} : a ≤ b → b ≤ c → a ≤ c :=
well_order.le_trans

protected def equiv (a b) :=
a ≤ b ∧ b ≤ a

local infix ` ≃ `: 50 := pre_ord.equiv

@[refl]
protected lemma equiv_refl (a) : a ≃ a :=
⟨by refl, by refl⟩

@[symm]
protected lemma equiv_symm {a b} : a ≃ b → b ≃ a
| ⟨h1, h2⟩ := ⟨h2, h1⟩

@[trans]
protected lemma equiv_trans {a b c} : a ≃ b → b ≃ c → a ≃ c
| ⟨h1, h2⟩ ⟨g1, g2⟩ := ⟨pre_ord.le_trans h1 g1, pre_ord.le_trans g2 h2⟩

lemma equivalence_equiv : equivalence pre_ord.equiv :=
⟨pre_ord.equiv_refl, @pre_ord.equiv_symm, @pre_ord.equiv_trans⟩

instance : has_le pre_ord := ⟨pre_ord.le⟩

protected def setoid : setoid pre_ord :=
{ r := pre_ord.equiv, iseqv := equivalence_equiv }

attribute [instance] pre_ord.setoid

end pre_ord

def ord := quotient pre_ord.setoid

namespace ord

instance (n) : well_order (fin n) :=
{  }

instance : well_order empty :=
{ lt := λ _ _, false,
  lt_irrefl := empty.rec_on _,
  lt_trans := empty.rec_on _,
  wf := ⟨empty.rec_on _⟩ }

def le (a b : ord) : Prop :=
quotient.rec_on a
    (λ a, quotient.rec_on b
        (λ b, a ≤ b)
    sorry)
sorry

instance : strict_order ord := {
    lt := ord.lt,
    lt_irrefl := begin intros a, induction a, intro h, cases h, end,
    lt_trans := _
}

protected def mk (α : Type) [h : well_order α] : ord :=
quotient.mk ⟨α, h⟩

protected def zero :=
ord.mk empty

end ord