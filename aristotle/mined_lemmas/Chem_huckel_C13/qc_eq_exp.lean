import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma qc_eq_exp (k : Fin 13) :
    qc k = Complex.exp (((2 * Real.pi * (k : ℕ) / 13 : ℝ) : ℂ) * Complex.I) := by
  rw [qc, zeta13, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the character `k`: `ζ^k + ζ^{-k} = 2 cos (2πk/13)`. -/
