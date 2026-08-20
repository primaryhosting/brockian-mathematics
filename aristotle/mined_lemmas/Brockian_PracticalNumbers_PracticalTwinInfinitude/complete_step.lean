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

lemma complete_step (hk : 0 < k) (hD : Complete D) (hle : k ≤ (∑ x ∈ D, x) + 1)
    (hdisj : Disjoint D (D.image (fun d => k * d))) :
    Complete (D ∪ D.image (fun d => k * d)) := by
  intro m hm
  rw [sum_union_image D k hk hdisj] at hm
  set S := ∑ x ∈ D, x with hS
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a ≤ S ∧ b ≤ S ∧ m = k * a + b := by
    rcases le_or_gt (m / k) S with h | h
    · refine ⟨m / k, m % k, h, ?_, (Nat.div_add_mod m k).symm⟩
      have := Nat.mod_lt m hk
      omega
    · have hkS : (S + 1) * k ≤ m := (Nat.le_div_iff_mul_le hk).mp h
      have e1 : (S + 1) * k = k * S + k := by ring
      have e2 : (1 + k) * S = S + k * S := by ring
      exact ⟨S, m - k * S, le_rfl, by omega, by omega⟩
  obtain ⟨A, hA, hAsum⟩ := hD a ha
  obtain ⟨B, hB, hBsum⟩ := hD b hb
  have hAsub : A.image (fun d => k * d) ⊆ D.image (fun d => k * d) :=
    Finset.image_subset_image hA
  have hdisj' : Disjoint (A.image (fun d => k * d)) B := hdisj.symm.mono hAsub hB
  refine ⟨A.image (fun d => k * d) ∪ B, ?_, ?_⟩
  · exact Finset.union_subset (hAsub.trans Finset.subset_union_right)
      (hB.trans Finset.subset_union_left)
  · rw [Finset.sum_union hdisj',
      Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk h), ← Finset.mul_sum,
      hAsum, hBsum, hab]

end Step

/-! ### Powers of two are practical -/

