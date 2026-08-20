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

lemma le_runLen {s : Finset ℕ} (h0 : 0 ∉ s) (t j : ℕ) (h : ∀ i < j, t - i ∈ s) :
    j ≤ runLen s t := by
  induction t generalizing j with
  | zero =>
      by_contra hc
      have : (0 : ℕ) - 0 ∈ s := h 0 (by omega)
      simp at this; exact h0 this
  | succ t ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · omega
      · have hmem : t + 1 ∈ s := by simpa using h 0 (by omega)
        simp only [runLen, if_pos hmem]
        have : j - 1 ≤ runLen s t := by
          refine ih (j - 1) ?_
          intro i hi
          have : t - i = t + 1 - (i + 1) := by omega
          rw [this]
          exact h (i + 1) (by omega)
        omega

