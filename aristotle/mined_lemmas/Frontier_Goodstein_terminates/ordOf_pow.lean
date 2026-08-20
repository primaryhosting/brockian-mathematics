/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- written as a plain block comment; it is repeated as a module docstring below.)

import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Hereditary base representations

For a base `b ≥ 2`, every positive natural number `n` can be written as
`n = b ^ e * c + r` with `e = Nat.log b n`, `1 ≤ c < b` and `r < b ^ e`, and iterating this
inside the exponent yields the *hereditary base-`b` representation* of `n`.

Two operations are defined by this recursion:

* `ordOf b n` : the ordinal obtained by replacing the base `b` by `ω` in the hereditary
  base-`b` representation of `n` (a "Goodstein ordinal", an ordinal `< ε₀`);
* `shiftBase b n` : the natural number obtained by replacing the base `b` by `b + 1`
  in the hereditary base-`b` representation of `n`.
-/


lemma ordOf_pow {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : ordOf b (b ^ k) = ω ^ ordOf b k := by
  have hbpos : 0 < b := by omega
  have hne : b ^ k ≠ 0 := Nat.ne_of_gt (pow_pos hbpos k)
  rw [ordOf_eq_of_ne_zero hne, Nat.log_pow hb (b := b) k, Nat.div_self (pow_pos hbpos k),
    Nat.mod_self, ordOf_zero, Nat.cast_one, mul_one, add_zero]

/-! ## The shift preserves the associated ordinal -/

