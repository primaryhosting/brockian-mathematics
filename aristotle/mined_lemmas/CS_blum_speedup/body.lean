import RequestProject.BlumTime

/-!
# The core of the speed-up construction

This file contains the (first-order, oracle-parametrised) combinatorial core of the
diagonal construction used in the proof of Blum's speed-up theorem.

The construction is parametrised by two functions:

* `rf : ℕ → ℕ`, the speed-up factor;
* `T : ℕ → ℕ`, an oracle giving the running time of the (self-referential) code under
  construction at a given input.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ### Small helpers -/

/-- Bounded universal quantifier, as a `Bool`. -/

def body (rf T : ℕ → ℕ) (z x : ℕ) : ℕ :=
  ((Denumerable.ofNat (List (ℕ × ℕ)) z.unpair.2).lookup x).getD
    (leastNotIn (vals rf T z.unpair.1 x))

/-! ### Congruence -/

/-- The two oracles `(rf, T)` and `(rf', T')` agree on everything that the member `n` of the
family consults at stage `x`. -/
