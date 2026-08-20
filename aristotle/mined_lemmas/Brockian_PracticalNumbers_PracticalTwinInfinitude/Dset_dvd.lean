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

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/

lemma Dset_dvd (i : ℕ) : ∀ d ∈ Dset i, d ∣ N i := by
  induction i with
  | zero =>
      intro d hd
      fin_cases hd <;> simp [N]
  | succ i ih =>
      intro d hd
      have hN : N (i + 1) = N i * F i := rfl
      rw [hN]
      rcases Finset.mem_union.mp hd with h | h
      · exact (ih d h).trans (dvd_mul_right _ _)
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
        have hd' : F i * e ∣ F i * N i := mul_dvd_mul_left _ (ih e he)
        rwa [mul_comm (F i) (N i)] at hd'

