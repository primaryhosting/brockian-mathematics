import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

lemma gapTuple_gap_range (a d k : ℕ) (hk : 0 < k) :
    (∀ h ∈ gapTuple a d k, a ≤ h ∧ h ≤ a + (k - 1) * d) ∧
      a ∈ gapTuple a d k ∧ a + (k - 1) * d ∈ gapTuple a d k := by
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    simp only [gapTuple, Finset.mem_image, Finset.mem_range] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    exact ⟨Nat.le_add_right _ _,
      Nat.add_le_add_left (Nat.mul_le_mul_right d (by omega)) a⟩
  · simp only [gapTuple, Finset.mem_image, Finset.mem_range]
    exact ⟨0, hk, by simp⟩
  · simp only [gapTuple, Finset.mem_image, Finset.mem_range]
    exact ⟨k - 1, by omega, rfl⟩

/--
**Singular Series Gaps 13501360.**

Let `k ≥ 1` and let `d` be divisible by every prime `p ≤ k`.  Then the length-`k`
arithmetic progression `{a, a+d, …, a+(k-1)d}` is an admissible tuple, and consequently
every Euler factor `1 - ν_p(H)/p` of its singular series is strictly positive.

This gives an infinite family of admissible gap ranges: the diameter of the tuple is
`(k-1)·d`, and the conclusion holds for every shift `a`.
-/
