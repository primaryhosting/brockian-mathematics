/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma w14_pow_add_pow (k : Fin 14) :
    w14 ^ k.val + w14 ^ (13 * k.val) = C14eigval k := by
  have h1 : w14 ^ (13 * k.val) * w14 ^ k.val = 1 := by
    rw [← pow_add, show 13 * k.val + k.val = 14 * k.val by ring, pow_mul, w14_pow_14, one_pow]
  have hinv : w14 ^ (13 * k.val) = (w14 ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hinv, w14_pow_eq_exp, ← Complex.exp_neg, C14eigval,
    show -((2 * Real.pi * k.val / 14 : ℝ) * Complex.I)
        = -((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I by ring,
    ← Complex.two_cos, Complex.ofReal_cos]

