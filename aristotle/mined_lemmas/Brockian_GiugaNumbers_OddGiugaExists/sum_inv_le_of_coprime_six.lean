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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite number `n > 1` such that every prime `p` dividing `n`
satisfies `p ∣ n / p - 1`. -/

lemma sum_inv_le_of_coprime_six {S : Finset ℕ}
    (hS : ∀ p ∈ S, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5)) :
    ∑ p ∈ S, (1 : ℚ) / p ≤ ∑ i ∈ range S.card, (1 : ℚ) / coprimeSixEnum i := by
  have hinv : ∀ p ∈ S, coprimeSixEnum (coprimeSixIndex p) = p :=
    fun p hp => coprimeSixEnum_index (hS p hp).1 (hS p hp).2
  have hinj : ∀ a ∈ S, ∀ b ∈ S, coprimeSixIndex a = coprimeSixIndex b → a = b := by
    intro a ha b hb hab
    rw [← hinv a ha, ← hinv b hb, hab]
  have hcard : (S.image coprimeSixIndex).card = S.card := Finset.card_image_of_injOn hinj
  have hsum : ∑ i ∈ S.image coprimeSixIndex, (1 : ℚ) / coprimeSixEnum i
      = ∑ p ∈ S, (1 : ℚ) / p := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun p hp => by rw [hinv p hp])
  rw [← hsum, ← hcard]
  exact sum_le_sum_range_of_antitone antitone_inv_coprimeSixEnum _

/-- Prime divisors of an odd Giuga number other than `3` are `≥ 5` and coprime to `6`. -/
