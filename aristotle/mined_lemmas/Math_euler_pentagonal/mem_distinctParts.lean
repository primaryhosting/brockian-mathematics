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

lemma mem_distinctParts {n : ℕ} {s : Finset ℕ} :
    s ∈ distinctParts n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  classical
  simp only [distinctParts, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum⟩
    have h1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exact absurd ha h0
      · exact h
    have h2 : a ≤ n := by
      rw [← hsum]; exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
    simp [Finset.mem_Icc, h1, h2]

