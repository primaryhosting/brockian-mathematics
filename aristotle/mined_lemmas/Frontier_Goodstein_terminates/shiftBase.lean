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


def shiftBase (b n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    (b + 1) ^ shiftBase b (Nat.log b n) * (n / b ^ Nat.log b n)
      + shiftBase b (n % b ^ Nat.log b n)
  termination_by n
  decreasing_by
  · exact Nat.log_lt_self b h
  · exact mod_pow_log_lt b n h

/-- The Goodstein sequence starting at `n`: `goodstein n 0 = n` (read in base `2`), and each
step rewrites the current value in hereditary base `k + 2`, bumps the base to `k + 3`, and
subtracts one. -/
