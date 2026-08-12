import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open scoped Pointwise

namespace AdditiveComb

variable {A B : Finset ℤ}

/-- The two "extremal translates" `A + {min B}` and `{max A} + B` meet in exactly one point,
namely `max A + min B`. -/
theorem inter_extremal_translates (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + {B.min' hB}) ∩ ({A.max' hA} + B) = {A.max' hA + B.min' hB} := by
  apply Finset.eq_singleton_iff_unique_mem.2
  constructor
  · exact Finset.mem_inter.2
      ⟨Finset.add_mem_add (A.max'_mem hA) (Finset.mem_singleton_self _),
       Finset.add_mem_add (Finset.mem_singleton_self _) (B.min'_mem hB)⟩
  · rintro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx₁
    obtain ⟨a', ha', b', hb', hab⟩ := Finset.mem_add.1 hx₂
    rw [Finset.mem_singleton] at hb ha'
    subst hb; subst ha'
    have h1 : a ≤ A.max' hA := A.le_max' a ha
    have h2 : B.min' hB ≤ b' := B.min'_le b' hb'
    omega

/-- **Sumset lower bound** (the Cauchy–Davenport analogue over `ℤ`, i.e. the base case of
Freiman's lemma): for finite nonempty sets `A B` of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
theorem sumset_lower_bound (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  have hsub : (A + {B.min' hB}) ∪ ({A.max' hA} + B) ⊆ A + B :=
    Finset.union_subset
      (Finset.add_subset_add_left (Finset.singleton_subset_iff.2 (B.min'_mem hB)))
      (Finset.add_subset_add_right (Finset.singleton_subset_iff.2 (A.max'_mem hA)))
  have hcard := Finset.card_le_card hsub
  have hunion :
      ((A + {B.min' hB}) ∪ ({A.max' hA} + B)).card + 1 = A.card + B.card := by
    have h := Finset.card_union_add_card_inter (A + {B.min' hB}) ({A.max' hA} + B)
    rw [inter_extremal_translates hA hB, Finset.card_singleton,
      Finset.card_add_singleton, Finset.card_singleton_add] at h
    exact h
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

