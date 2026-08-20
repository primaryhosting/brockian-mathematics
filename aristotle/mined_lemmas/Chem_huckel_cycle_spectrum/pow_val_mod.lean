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

lemma pow_val_mod (μ : ℂ) (n : ℕ) (h : μ ^ n = 1) (a : ℕ) : μ ^ (a % n) = μ ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

