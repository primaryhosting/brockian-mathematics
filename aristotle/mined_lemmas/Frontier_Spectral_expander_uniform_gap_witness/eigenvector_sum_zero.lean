/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma eigenvector_sum_zero {k : ℕ} {μ : ℝ} {f : Cube k → ℝ} (hμ : μ ≠ 0)
    (hf : (hypercube k).lapMatrix ℝ *ᵥ f = μ • f) : ∑ x : Cube k, f x = 0 := by
  have hcol : ∀ y : Cube k, ∑ x : Cube k, (hypercube k).lapMatrix ℝ x y = 0 := by
    intro y
    have hs := SimpleGraph.isSymm_lapMatrix (R := ℝ) (hypercube k)
    have h0 : ∑ x : Cube k, (hypercube k).lapMatrix ℝ y x = 0 := by
      have h := congrFun (SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) (hypercube k)) y
      simpa [Matrix.mulVec, dotProduct] using h
    rw [← h0]
    exact Finset.sum_congr rfl fun x _ => hs.apply y x
  have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ f) x = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [← Finset.sum_mul, hcol y, zero_mul]
  rw [hf] at h1
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h1
  exact (mul_eq_zero.1 h1).resolve_left hμ

/-- Every nonzero Laplacian eigenvalue of the hypercube is at least `2`. -/
