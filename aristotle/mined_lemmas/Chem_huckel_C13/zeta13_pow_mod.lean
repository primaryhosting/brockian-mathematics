/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/

lemma zeta13_pow_mod (n : ℕ) : zeta13 ^ (n % 13) = zeta13 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, zeta13_pow_13, one_pow, one_mul]

/-- The additive character `m ↦ exp (2πi m /13)` on `Fin 13`. -/
