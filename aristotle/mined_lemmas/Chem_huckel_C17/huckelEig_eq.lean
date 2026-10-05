/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma huckelEig_eq (k : Fin 17) :
    huckelEig k = zeta17 ^ ((k : ℕ)) + zeta17 ^ (16 * (k : ℕ)) := by
  have hz : zeta17 ^ ((k : ℕ)) = Complex.exp (2 * Real.pi * I * (k : ℕ) / 17) := by
    rw [zeta17, ← Complex.exp_nat_mul]; ring_nf
  have hz' : zeta17 ^ (16 * (k : ℕ)) = Complex.exp (-(2 * Real.pi * I * (k : ℕ) / 17)) := by
    have h1 : zeta17 ^ ((k : ℕ)) * zeta17 ^ (16 * (k : ℕ)) = 1 := by
      rw [← pow_add]
      have h : (k : ℕ) + 16 * (k : ℕ) = 17 * (k : ℕ) := by ring
      rw [h, pow_mul, zeta17_pow_seventeen, one_pow]
    rw [hz] at h1
    rw [Complex.exp_neg]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [hz, hz', huckelEig,
    show ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)
        = 2 * Complex.cos ((2 * Real.pi * (k : ℕ) / 17 : ℝ) : ℂ) by
      push_cast [Complex.ofReal_cos]; ring,
    Complex.two_cos]
  push_cast
  ring_nf

