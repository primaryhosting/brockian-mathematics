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

private lemma exp_pow_five (k : ℕ) :
    (Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)) ^ 5 = 1 := by
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [show (5 : ℂ) * ((2 * (Real.pi : ℂ) * k / 5) * Complex.I)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

/-- `exp (2πik/5) + exp (2πik/5)⁴ = 2 cos (2πk/5)`. -/
