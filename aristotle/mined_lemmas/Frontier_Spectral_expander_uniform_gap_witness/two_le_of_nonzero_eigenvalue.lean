/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a point of the discrete cube `Fin k → Bool`. -/

lemma two_le_of_nonzero_eigenvalue {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) {v : (Fin k → Bool) → ℝ}
    (hv0 : v ≠ 0) (hv : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) : 2 ≤ μ := by
  have hsum := sum_eq_zero_of_eigenvector hμ hv
  have hq : dirichlet k v / 2 = μ * ∑ x : Fin k → Bool, v x ^ 2 := by
    rw [← dotProduct_lapMatrix_hypercube, hv]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hpos : 0 < ∑ x : Fin k → Bool, v x ^ 2 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv0
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨x, Finset.mem_univ x, ?_⟩
    have : v x ≠ 0 := hx
    positivity
  have hp := poincare k v
  rw [hsum] at hp
  have hn : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [hp, hq, hpos, hn, mul_pos hn hpos]

/-- For every `k ≥ 1`, the smallest nonzero Laplacian eigenvalue of the hypercube `Q_k`
is exactly `2`. -/
