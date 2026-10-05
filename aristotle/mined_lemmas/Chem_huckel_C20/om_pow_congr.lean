/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma om_pow_congr {m n : ℕ} (h : m % 20 = n % 20) : om ^ m = om ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 20]
  conv_rhs => rw [← Nat.div_add_mod n 20]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow20, one_pow, one_pow, h]

