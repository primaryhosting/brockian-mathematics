import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma ec_add_ec_neg (k : ZMod 9) :
    ec k + ec (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 9) : ℝ) : ℂ) := by
  have hinv : ec (-k) = (ec k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← ec_add, neg_add_cancel, ec_zero])
  rw [hinv, ec_eq_exp k, ← Complex.exp_neg,
    show -(((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I)
      = (-((2 * Real.pi * k.val / 9 : ℝ) : ℂ)) * Complex.I by ring, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

/-- **Hückel theory for the cycle `C₉`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₉` if and only if `μ = 2 cos (2πk/9)` for some
`k ∈ {0, 1, …, 8}`. -/
