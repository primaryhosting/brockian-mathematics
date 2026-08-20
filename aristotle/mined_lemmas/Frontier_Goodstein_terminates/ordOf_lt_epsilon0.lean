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


lemma ordOf_lt_epsilon0 (b n : ℕ) : ordOf b n < ε₀ := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Ordinal.epsilon_pos 0]
  · have hn : n ≠ 0 := by omega
    rw [ordOf_eq_of_ne_zero hn]
    exact add_lt_epsilon0
      (mul_lt_epsilon0 (opow_lt_epsilon0 (IH _ (Nat.log_lt_self b hn)))
        (Ordinal.natCast_lt_epsilon _ 0))
      (IH _ (mod_pow_log_lt b n hn))

/-! ## Goodstein's theorem -/

