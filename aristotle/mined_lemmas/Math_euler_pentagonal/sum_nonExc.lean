import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma sum_nonExc (n : ℕ) : ∑ S ∈ nonExcSets n, ((-1 : ℤ)) ^ S.card = 0 := by
  refine Finset.sum_involution (fun S _ => franklin S) (fun S hS => ?_) (fun S hS _ => ?_)
    (fun S hS => (franklin_props hS).1) (fun S hS => (franklin_props hS).2.2)
  · show ((-1 : ℤ)) ^ S.card + ((-1 : ℤ)) ^ (franklin S).card = 0
    have := (franklin_props hS).2.1
    linarith
  · intro h
    replace h : franklin S = S := h
    have h2 := (franklin_props hS).2.1
    rw [h] at h2
    have : ((-1 : ℤ)) ^ S.card ≠ 0 := pow_ne_zero _ (by norm_num)
    apply this
    linarith

/-! ### Arithmetic of pentagonal numbers -/

