/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer

Using classical logic, defines an inverse function.
-/
universes u

namespace set

variables {α β : Type u}

local attribute [instance] classical.prop_decidable
open classical function

noncomputable definition inv_fun (f : α → β) [inhabited α] (y : β) : α :=
if H : ∃ x, f x = y then some H else default _

lemma inv_fun_pos {f : α → β} [inhabited α] {y : β}
  (h : ∃ x, f x = y) : f (inv_fun f y) = y :=
begin unfold inv_fun, simp [dif_pos, *], apply some_spec h end

lemma inv_fun_neg {f : α → β} [inhabited α] {y : β}
  (H : ¬ ∃ x, f x = y) : inv_fun f y = default _ :=
dif_neg H

variables {f : α → β}

lemma right_inverse_inv_fun (h : surjective f) [inhabited α] :
  right_inverse (inv_fun f) f | b :=
inv_fun_pos (h _)

lemma left_inverse_inv_fun (h : injective f) [inhabited α] :
  left_inverse (inv_fun f) f | b :=
begin
have: ∃ x, f x = f b := ⟨b, rfl⟩,
apply h, simp [@inv_fun_pos _ _ f _ _ this],
end

end set

open set