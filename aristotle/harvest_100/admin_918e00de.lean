import Mathlib
-- (Lean 4 requires `import` lines to precede any module docstring, so the
-- requested header comment appears immediately below the import.)
/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Pointwise

namespace AdditiveComb

/-- The two "extremal slices" `A + {min B}` and `{max A} + B` of the sumset `A + B`
meet exactly in the single element `max A + min B`. -/
lemma inter_slices_eq_singleton {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨?_, ?_⟩, ?_⟩
  · exact add_mem_add (A.max'_mem hA) (mem_singleton_self _)
  · exact add_mem_add (mem_singleton_self _) (B.min'_mem hB)
  · intro x hx
    rw [mem_inter, mem_add, mem_add] at hx
    obtain ⟨⟨a, ha, b, hb, rfl⟩, ⟨a', ha', b', hb', h⟩⟩ := hx
    rw [mem_singleton] at hb ha'
    subst hb; subst ha'
    have hmax : a ≤ A.max' hA := A.le_max' a ha
    have hmin : B.min' hB ≤ b' := B.min'_le b' hb'
    have : a = A.max' hA := le_antisymm hmax (by omega)
    rw [this]

/-- **Sumset lower bound over `ℤ`** (the Cauchy–Davenport analogue over the integers,
also the base case of Freiman's lemma): for nonempty finite sets of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
theorem sumset_lower_bound {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  have key : (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} :=
    inter_slices_eq_singleton hA hB
  have hsub : (A + {B.min' hB}) ∪ ({A.max' hA} + B) ⊆ A + B :=
    union_subset
      (add_subset_add_left (singleton_subset_iff.2 (B.min'_mem hB)))
      (add_subset_add_right (singleton_subset_iff.2 (A.max'_mem hA)))
  have hcard := card_le_card hsub
  have hue : ((A + {B.min' hB}) ∪ ({A.max' hA} + B)).card
      + ((A + {B.min' hB}) ∩ ({A.max' hA} + B)).card
      = (A + {B.min' hB}).card + ({A.max' hA} + B).card :=
    card_union_add_card_inter _ _
  rw [key, card_singleton, card_add_singleton, card_singleton_add] at hue
  omega

end AdditiveComb

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

