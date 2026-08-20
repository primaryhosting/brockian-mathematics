/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Complex

/-- The primitive 18-th root of unity `exp(2πi/18)`. -/

lemma om_pow_add_inv (k : Fin 18) :
    om ^ (k : ℕ) + om ^ (17 * (k : ℕ)) = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 18) : ℂ) := by
  have hz : om ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 18 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : om ^ (17 * (k : ℕ)) = Complex.exp (-(2 * Real.pi * (k : ℕ) / 18 : ℝ) * Complex.I) := by
    have h1 : om ^ (17 * (k : ℕ)) * om ^ (k : ℕ) = 1 := by
      rw [← pow_add]
      have h18 : 17 * (k : ℕ) + (k : ℕ) = 18 * (k : ℕ) := by ring
      rw [h18, pow_mul, om_pow_18, one_pow]
    have hne : om ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (by
      simp [om, Complex.exp_ne_zero])
    have h2 := eq_div_of_mul_eq hne h1
    rw [h2, hz, one_div, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hz, hz', Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

