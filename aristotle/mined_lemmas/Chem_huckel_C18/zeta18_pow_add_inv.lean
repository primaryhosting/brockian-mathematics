/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma zeta18_pow_add_inv (k : Fin 18) :
    (zeta18 ^ (k : ℕ)) ^ 17 + zeta18 ^ (k : ℕ) = ((huckelEnergy k : ℝ) : ℂ) := by
  have h17 : (zeta18 ^ (k : ℕ)) ^ 17 = (zeta18 ^ (k : ℕ))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact zeta18_pow_pow_18 _
  rw [h17, zeta18_pow_eq_exp, ← Complex.exp_neg, huckelEnergy]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]
  ring_nf

