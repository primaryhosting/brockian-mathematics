/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the 5-cycle `C₅`

The Hückel secular problem for the cyclic polyene `C₅H₅` reduces (after removing the
Coulomb integral `α` and dividing by the resonance integral `β`) to the eigenvalue
problem for the adjacency matrix of the cycle graph `C₅`.

The main result `Chem.huckel_C5` states that the eigenvalues of that adjacency matrix
are exactly the five numbers `2 * cos (2 * π * k / 5)`, `k = 0, 1, 2, 3, 4`
(equivalently `2`, `(√5 - 1)/2` twice and `-(√5 + 1)/2` twice).
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where `α = 0`, `β = 1`). -/

private lemma exp_add_pow_four (k : ℕ) :
    Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)
        + (Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)) ^ 4
      = ((2 * Real.cos (2 * Real.pi * k / 5) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * k / 5 with ht
  have h5 := exp_pow_five k
  rw [← ht] at h5
  have h4 : Complex.exp ((t : ℂ) * Complex.I) ^ 4 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have e : ((4 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = (5 : ℕ) * ((t : ℂ) * Complex.I) + (-(t : ℂ) * Complex.I) := by push_cast; ring
    rw [← Complex.exp_nat_mul, e, Complex.exp_add, Complex.exp_nat_mul, h5, one_mul]
  rw [h4]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]

