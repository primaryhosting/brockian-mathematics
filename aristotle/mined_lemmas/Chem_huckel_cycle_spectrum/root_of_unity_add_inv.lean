/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

lemma root_of_unity_add_inv (n k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
        + ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k)⁻¹
      = 2 * Real.cos (2 * Real.pi * k / n) := by
  rw [← Complex.exp_nat_mul]
  rw [show ((k : ℂ) * (2 * Real.pi * Complex.I / n)) = ((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [← Complex.exp_neg, neg_mul_eq_neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- **Hückel cycle spectrum.** The eigenvalues of the adjacency matrix of the cycle graph
`C n` (`n ≥ 3`) are exactly the numbers `2 cos (2 π k / n)` for `k = 0, …, n - 1`;
these are the Hückel π-electron energies of an `n`-membered conjugated ring
(in units of the resonance integral `β`, measured from the Coulomb integral `α`). -/
