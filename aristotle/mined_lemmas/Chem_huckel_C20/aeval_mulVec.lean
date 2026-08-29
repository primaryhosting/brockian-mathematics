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

lemma aeval_mulVec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {v : n → ℂ} {c : ℂ}
    (h : M *ᵥ v = c • v) (g : ℂ[X]) : (aeval M g) *ᵥ v = (g.eval c) • v := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [Matrix.add_mulVec, hp, hq, add_smul]
  | monomial d a =>
    simp only [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one]
    rw [smul_mul_assoc, one_mul, smul_mulVec, pow_mulVec h d, smul_smul]

/-! ## The 20-th root of unity -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/
