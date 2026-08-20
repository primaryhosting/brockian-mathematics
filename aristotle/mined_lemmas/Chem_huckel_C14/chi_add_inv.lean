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

lemma chi_add_inv (k : Fin 14) : chi k + (chi k)⁻¹ = hlam k := by
  have h1 : chi k = Complex.exp (((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I) :=
    chi_eq_exp k
  have h2 : (chi k)⁻¹
      = Complex.exp (-(((2 * Real.pi * (k : ℝ) / 14 : ℝ) : ℂ) * Complex.I)) := by
    rw [h1, ← Complex.exp_neg]
  rw [h2, h1, hlam]
  push_cast
  rw [Complex.two_cos, neg_mul]

