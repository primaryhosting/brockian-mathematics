import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_eq_exp (k : Fin 14) :
    chi k = Complex.exp (((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I) := by
  rw [chi, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

