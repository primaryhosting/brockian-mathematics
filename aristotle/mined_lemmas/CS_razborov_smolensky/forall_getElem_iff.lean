import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma forall_getElem_iff {α : Type*} (L : List α) (p : α → Prop) :
    (∀ pos : Fin L.length, p L[pos]) ↔ ∀ a ∈ L, p a := by
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    exact h ⟨i, hi⟩
  · intro h pos
    exact h _ (List.getElem_mem pos.2)

/-- **Razborov's approximation lemma.**  Every gate of a circuit is computed, outside a small
set of bad inputs, by a function of low degree over `ZMod q`. -/
