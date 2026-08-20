/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma zeta_pow_mod (hN : N ≠ 0) (x : ℕ) : (zeta N) ^ (x % N) = (zeta N) ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x N, pow_add, pow_mul, zeta_pow_N hN, one_pow, one_mul]

/-- The standard additive character `a ↦ exp (2πi a / N)` on `ZMod N`. -/
