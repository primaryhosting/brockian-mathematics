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

lemma sum_not_fixed (n : ℕ) :
    ∑ s ∈ (distinctParts n).filter (fun s => ¬ IsFixed s), (-1 : ℤ) ^ s.card = 0 := by
  classical
  refine Finset.sum_involution (fun s _ => franklin s) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    rw [franklin_sign h0 hne hexc]; ring
  · intro a ha _
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    intro hcon
    have h := franklin_sign h0 hne hexc
    simp only at hcon
    rw [hcon] at h
    have hp : (-1 : ℤ) ^ a.card ≠ 0 := by positivity
    exact hp (by linarith)
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha ⊢
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    refine ⟨⟨franklin_zero_not_mem h0 hne hexc, by rw [franklin_sum h0 hne hexc, hsum]⟩,
      Finset.nonempty_iff_ne_empty.1 franklin_nonempty,
      franklin_not_exc h0 hne hexc⟩
  · intro a ha
    simp only [Finset.mem_filter, mem_distinctParts, IsFixed, not_or] at ha
    obtain ⟨⟨h0, hsum⟩, hne0, hexc⟩ := ha
    have hne : a.Nonempty := Finset.nonempty_iff_ne_empty.2 hne0
    exact franklin_franklin h0 hne hexc

