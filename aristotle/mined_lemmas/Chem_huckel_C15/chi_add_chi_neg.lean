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

lemma chi_add_chi_neg (k : ZMod 15) :
    chi k + chi (-k) = 2 * Real.cos (2 * Real.pi * k.val / 15) := by
  have hinv : chi (-k) = Complex.exp (-((2 * Real.pi * k.val / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [chi_neg, chi_eq_exp, ← Complex.exp_neg]
    congr 1
    ring
  rw [chi_eq_exp, hinv, Complex.ofReal_cos, ← Complex.two_cos]

/-- Each Fourier vector is an eigenvector with eigenvalue `2cos(2πk/15)`. -/
