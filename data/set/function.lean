import algebra.order
import algebra.lattice.complete_lattice

universes u v

namespace set
variables {α : Type u} {β : α → Type v}

def graph (f : ∀ a, β a) (a : α) (b : β a) : Prop :=
f a = b

namespace graph

def partial_fun (g : ∀ a, β a → Prop) :=
∀ a b1 b2, g a b1 → g a b2 → b1 = b2

lemma graph_pfn (f : ∀ a, β a) : partial_fun (graph f)
| a b1 b2 hb1 hb2 := by simp [*, graph] at *

def injective (g : ∀ a, β a → Prop) :=
∀ a1 a2 b1 b2, g a1 b1 → g a2 b2 → b1 == b2 → a1 = a2

def surjective (g : ∀ a, β a → Prop) :=
∀ a, ∃ b, g a b

def dom (g : ∀ a, β a → Prop) : set α
| a := ∃ b, g a b

def total (g : ∀ a, β a → Prop) :=
∀ a, a ∈ dom g

lemma dom_graph (f : ∀ a, β a) : total (graph f)
| a := ⟨f a, rfl⟩

noncomputable def apply (g : ∀ a, β a → Prop) : ∀ a ∈ dom g, β a
| a ha := classical.some ha

lemma apply_spec (g : ∀ a, β a → Prop) : ∀ a ∈ dom g, g a (apply g a H)
| a H := classical.some_spec H

lemma apply_graph (f : ∀ a, β a) (a : α) : apply (graph f) a (dom_graph _ _) = f a :=
graph_pfn f _ _ _ (apply_spec _ _ _) rfl

end graph

end set