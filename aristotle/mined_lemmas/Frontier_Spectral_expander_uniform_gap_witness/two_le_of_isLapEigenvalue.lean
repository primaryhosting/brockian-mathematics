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


lemma two_le_of_isLapEigenvalue {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) (h : IsLapEigenvalue k μ) :
    2 ≤ μ := by
  obtain ⟨f, hf0, hf⟩ := h
  have hmean := eigenvector_sum_zero hμ hf
  have hq := quadratic_form_eq f
  rw [hf] at hq
  have hq' : μ * ∑ x : Cube k, (f x) ^ 2 = Dir k f / 2 := by
    rw [← hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hpos : 0 < ∑ x : Cube k, (f x) ^ 2 := by
    refine Finset.sum_pos' (fun x _ => sq_nonneg _) ?_
    by_contra hcon
    push_neg at hcon
    apply hf0
    funext x
    have hx := hcon x (Finset.mem_univ x)
    have : (f x) ^ 2 = 0 := le_antisymm hx (sq_nonneg _)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hP := poincare k f hmean
  nlinarith [hP, hq', hpos]

/-- For `k ≥ 1`, the value `2` is an eigenvalue of the hypercube Laplacian:
the character `x ↦ (-1)^{x_0}` is an eigenvector with eigenvalue `2`. -/
