import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma zeta_pow_add_inv (k : Fin 18) :
    (zeta ^ (k : ℕ)) ^ 17 + zeta ^ (k : ℕ) = mu k := by
  have hz : zeta ^ (k : ℕ) = Complex.exp (((2 * Real.pi * (k : ℕ) / 18 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h18 : (zeta ^ (k : ℕ)) ^ 18 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
  have h17 : (zeta ^ (k : ℕ)) ^ 17 = (zeta ^ (k : ℕ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h18)
  rw [h17, hz, ← Complex.exp_neg, mu, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

