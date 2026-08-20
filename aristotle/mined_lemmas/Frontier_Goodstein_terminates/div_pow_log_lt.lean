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


lemma div_pow_log_lt {b n : ℕ} (hb : 2 ≤ b) : n / b ^ Nat.log b n < b := by
  have hlt : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb n
  have := Nat.div_lt_of_lt_mul (by simpa [pow_succ] using hlt)
  simpa using this

/-! ## Ordinal estimates -/

/-- A "carry" estimate: if `X < ω ^ A` and `A < B` then `ω ^ A * c + X < ω ^ B`. -/
