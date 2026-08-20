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


lemma opow_mul_add_lt_opow {A B X : Ordinal} {c : ℕ} (hAB : A < B) (hX : X < ω ^ A) :
    ω ^ A * (c : Ordinal) + X < ω ^ B := by
  calc ω ^ A * (c : Ordinal) + X < ω ^ A * (c : Ordinal) + ω ^ A := add_lt_add_right hX _
    _ = ω ^ A * ((c : Ordinal) + 1) := by rw [mul_add, mul_one]
    _ ≤ ω ^ A * ω := by
        refine mul_le_mul_right ?_ _
        rw [show ((c : Ordinal) + 1) = ((c + 1 : ℕ) : Ordinal) by push_cast; rfl]
        exact le_of_lt (Ordinal.nat_lt_omega0 _)
    _ = ω ^ (A + 1) := by rw [Ordinal.add_one_eq_succ, Ordinal.opow_succ]
    _ ≤ ω ^ B := by
        refine Ordinal.opow_le_opow_right Ordinal.omega0_pos ?_
        rwa [Ordinal.add_one_eq_succ, Order.succ_le_iff]

/-- A "digit" estimate: if `X < ω ^ A` and `c < d` then `ω ^ A * c + X < ω ^ A * d`. -/
