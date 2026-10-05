import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


lemma det_A_sub (μ : ℂ) : (A14 - μ • (1 : Matrix (Fin 14) (Fin 14) ℂ)).det
    = ∏ k : Fin 14, (lam k - μ) := by
  have hmul : (A14 - μ • 1) * P14 = P14 * (Matrix.diagonal lam - μ • 1) := by
    rw [sub_mul, mul_sub, A_mul_P, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hdiag : (Matrix.diagonal lam - μ • (1 : Matrix (Fin 14) (Fin 14) ℂ))
      = Matrix.diagonal (fun k => lam k - μ) := by
    ext a b
    by_cases h : a = b <;> simp [h]
  rw [hdiag, Matrix.det_diagonal, mul_comm P14.det] at hdet
  exact mul_right_cancel₀ det_P_ne_zero hdet

/-- **Hückel theory for the cyclic polyene C₁₄.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₄` (the Hückel matrix of C₁₄ in units where `α = 0`,
`β = 1`) if and only if `μ = 2 cos (2πk/14)` for some `k = 0, …, 13`. -/
