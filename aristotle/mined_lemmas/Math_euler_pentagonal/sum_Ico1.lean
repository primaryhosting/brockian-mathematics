/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/

lemma sum_Ico1 (k : ℕ) : 2 * (∑ i ∈ Finset.Ico k (2 * k), i) + k = 3 * k * k := by
  have h3 : (∑ i ∈ Finset.range k, i) + ∑ i ∈ Finset.Ico k (2 * k), i
      = ∑ i ∈ Finset.range (2 * k), i := by
    simp only [Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have h1 : (∑ i ∈ Finset.range k, i) * 2 = k * (k - 1) := Finset.sum_range_id_mul_two k
  have h2 : (∑ i ∈ Finset.range (2 * k), i) * 2 = (2 * k) * (2 * k - 1) :=
    Finset.sum_range_id_mul_two (2 * k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
    have e1 : (t + 1) - 1 = t := by omega
    have e2 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    nlinarith [h1, h2, h3]

