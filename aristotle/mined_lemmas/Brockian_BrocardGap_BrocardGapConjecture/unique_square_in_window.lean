import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Setting

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are
`n = 4, 5, 7`, and it is an open problem whether there are others.

The *Brocard gap* statement formalised here is the quantitative "sparseness of squares just
above `n !`" phenomenon underlying the conjecture:

* consecutive squares just above `n !` are more than `Nat.sqrt (n !)` apart, so the window
  `(n !, n ! + Nat.sqrt (n !)]` contains **at most one** perfect square;
* for `n ≥ 8` this window has length at least `n ^ 2`, because `n ^ 4 ≤ n !` (proved by
  induction on `n`);
* consequently any Brocard solution `n ! + 1 = m ^ 2` with `n ≥ 8` has `m > n ^ 2` and yields
  the factorisation `n ! = (m - 1) * (m + 1)` of `n !` into two factors differing by `2`.
-/

open scoped Nat

namespace Brockian
namespace BrocardGap

/-- The Brocard gap window at `n`: the integers strictly above `n !` and at most
`n ! + Nat.sqrt (n !)`. -/

theorem unique_square_in_window {n a b : ℕ}
    (ha : a ^ 2 ∈ window n) (hb : b ^ 2 ∈ window n) : a = b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have key : ∀ x y : ℕ, n ! < x ^ 2 → y ^ 2 ≤ n ! + Nat.sqrt (n !) → x < y → False := by
    intro x y hx1 hy2 hxy
    have hx : Nat.sqrt (n !) < x := sqrt_lt_of_lt_sq hx1
    have h1 : (x + 1) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hxy 2
    have h2 : (x + 1) ^ 2 = x ^ 2 + (2 * x + 1) := by ring
    omega
  rcases lt_trichotomy a b with h | h | h
  · exact absurd h (fun hlt => key a b ha1 hb2 hlt)
  · exact h
  · exact absurd h (fun hlt => key b a hb1 ha2 hlt)

/-- **Reduction of Brocard solutions.** A solution `n ! + 1 = m ^ 2` with `n ≥ 8` forces
`m > n ^ 2` and exhibits `n !` as a product of two integers differing by `2`. -/
