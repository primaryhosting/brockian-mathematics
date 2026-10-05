import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma chi_eq_exp (k : ZMod 15) :
    chi k = Complex.exp ((2 * Real.pi * k.val / 15 : ℝ) * Complex.I) := by
  rw [chi, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the `k`-th Fourier mode. -/
