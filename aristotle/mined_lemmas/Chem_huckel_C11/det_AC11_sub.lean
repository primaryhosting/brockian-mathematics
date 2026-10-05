/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/

lemma det_AC11_sub (mu : ℂ) :
    (AC11 - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)).det = ∏ k : ZMod 11, (lam k - mu) := by
  rw [AC11_sub_smul_one, Matrix.det_mul, Matrix.det_mul, diagonal_sub_smul_one,
    Matrix.det_diagonal]
  rw [show F.det * ∏ k : ZMod 11, (lam k - mu) = (∏ k : ZMod 11, (lam k - mu)) * F.det by ring,
    mul_assoc, det_F_mul_det_Finv, mul_one]

/-! ## The Hückel spectrum -/

/-- **Hückel spectrum of the cycle C₁₁.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` if and only if `μ = 2 cos (2πk/11)` for some
`k ∈ {0, 1, …, 10}`. -/
