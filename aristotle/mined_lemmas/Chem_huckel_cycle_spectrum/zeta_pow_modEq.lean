import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma zeta_pow_modEq {n a b : ℕ} (hn : n ≠ 0) (h : a ≡ b [MOD n]) :
    zeta n ^ a = zeta n ^ b :=
  pow_eq_pow_of_modEq h (isPrimitiveRoot_zeta hn).pow_eq_one

/-- The `k`-th power of `zeta n` written as a complex exponential of a real angle. -/
