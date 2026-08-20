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


lemma goodstein_descent (n k : ℕ) (h : goodstein n k ≠ 0) :
    ordOf (k + 3) (goodstein n (k + 1)) < ordOf (k + 2) (goodstein n k) := by
  have hb : 2 ≤ k + 2 := by omega
  have hSne : shiftBase (k + 2) (goodstein n k) ≠ 0 := shiftBase_ne_zero h
  have hlt : goodstein n (k + 1) < shiftBase (k + 2) (goodstein n k) := by
    rw [goodstein]
    omega
  have hmono := ordOf_strictMono (show 2 ≤ k + 2 + 1 by omega) hlt
  rw [ordOf_shiftBase hb] at hmono
  simpa using hmono

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
