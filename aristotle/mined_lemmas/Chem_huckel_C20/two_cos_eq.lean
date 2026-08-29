import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma two_cos_eq (k : ℕ) (hk : k ≤ 20) :
    ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) = w ^ k + w ^ (20 - k) := by
  have hmul : w ^ k * w ^ (20 - k) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hk, w_pow_twenty]
  have hne : (w : ℂ) ^ k ≠ 0 := by
    rw [w_pow_eq_exp]; exact Complex.exp_ne_zero _
  have hinv : w ^ (20 - k) = (w ^ k)⁻¹ := by
    field_simp
    linear_combination hmul
  rw [hinv, w_pow_eq_exp, Complex.ofReal_mul, Complex.ofReal_cos, ← Complex.exp_neg,
    show ((2 : ℝ) : ℂ) = 2 from by norm_num, Complex.two_cos]
  ring_nf

/-! ## The cyclic shift matrix and the adjacency matrix of `C₂₀` -/

/-- The cyclic shift matrix on `Fin 20`. -/
