/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma node16_add_inv (k : Fin 16) :
    node16 k + node16 k ^ 15 = (huckelEigenvalue k : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 16 with ht
  have hx : node16 k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [node16, zeta16, ← Complex.exp_nat_mul]
    congr 1
    push_cast [ht]
    ring
  have hinv : node16 k ^ 15 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h16 : node16 k ^ 15 * node16 k = 1 := by
      rw [← pow_succ]; exact node16_pow_16 k
    have h2 : Complex.exp (-(t : ℂ) * Complex.I) * node16 k = 1 := by
      rw [hx, ← Complex.exp_add]
      simp
    exact mul_right_cancel₀ (node16_ne_zero k) (h16.trans h2.symm)
  rw [hinv, hx, huckelEigenvalue, ← ht]
  push_cast
  exact (Complex.two_cos _).symm

