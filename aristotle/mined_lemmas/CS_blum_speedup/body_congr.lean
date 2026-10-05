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

theorem body_congr {rf rf' T T' : ℕ → ℕ} {n d x : ℕ} (h : Agree rf rf' T T' n x) :
    body rf T (Nat.pair n d) x = body rf' T' (Nat.pair n d) x := by
  unfold body
  simp only [Nat.unpair_pair]
  rw [vals_congr h]

end CS

import Mathlib

/-!
# A running-time measure for `Nat.Partrec.Code`

`Nat.Partrec.Code.evaln k c x` runs the code `c` on input `x` with "fuel" `k`.
We define `CS.time c x` to be the least amount of fuel that suffices, which is a
Blum complexity measure for the programming system `Nat.Partrec.Code`:

* `CS.time c x` is defined exactly when `c` halts on `x`;
* the relation `CS.time c x ≤ k` is decidable (it is `(evaln k c x).isSome`).
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- `Halts c x` means that the code `c` converges on input `x`. -/
