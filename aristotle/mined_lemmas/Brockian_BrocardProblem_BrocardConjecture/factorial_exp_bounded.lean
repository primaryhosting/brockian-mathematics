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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede every other command, including module
-- docstrings, so the header above is a plain comment and is repeated verbatim as the
-- module docstring below.)

import Mathlib
import Brockian.BrocardProblem.SmallCases

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

Brocard's problem asks for all solutions of `n ! + 1 = m ^ 2`; the associated conjecture
(Brocard, Ramanujan) is that the only ones are `n = 4, 5, 7` (the *Brown numbers*).  The
conjecture is open.  This file contains:

* `Brockian.BrocardProblem.BrocardConjecture` — the statement of the conjecture;
* `Brockian.BrocardProblem.brown_numbers` — the three known solutions;
* `Brockian.BrocardProblem.brocard_below_301` — an unconditional verification of the
  conjecture for all `n < 301` (proved in `Brockian.BrocardProblem.SmallCases`);
* `Brockian.BrocardProblem.brocardConjecture_iff_ge_301` — the resulting reduction of the
  conjecture to the range `n ≥ 301`;
* `Brockian.BrocardProblem.brocard_finite_of_abc` — a conditional reduction: the `ε = 1/2`
  case of the `abc` conjecture (stated as `ABCConjectureHalf`) implies that Brocard's
  equation has only finitely many solutions.  This is the classical argument of Overholt.
-/

namespace Brockian
namespace BrocardProblem

open Finset Nat

/-! ### Brocard's conjecture -/

/-- **Brocard's conjecture**: the only natural numbers `n` for which `n ! + 1` is a perfect
square are `n = 4, 5, 7`. -/

theorem factorial_exp_bounded (D B : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n ! ≤ D * B ^ n → n ≤ N := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · refine ⟨0, fun n hn => ?_⟩
    by_contra h
    rw [Nat.zero_pow (by omega), Nat.mul_zero, Nat.le_zero] at hn
    exact absurd hn (Nat.factorial_pos n).ne'
  set k := 2 * B with hk
  refine ⟨max k (D * k ^ k), fun n hn => ?_⟩
  rcases lt_or_ge n k with h | h
  · exact le_trans (le_of_lt h) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have h1 : k ^ (n - k) ≤ n ! :=
      le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos k))
        (Nat.factorial_mul_pow_sub_le_factorial h)
    have h2 : k ^ n ≤ n ! * k ^ k := by
      calc k ^ n = k ^ (n - k) * k ^ k := by rw [← pow_add]; congr 1; omega
        _ ≤ n ! * k ^ k := Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ n * B ^ n ≤ D * B ^ n * k ^ k := by
      calc 2 ^ n * B ^ n = k ^ n := by rw [hk, mul_pow]
        _ ≤ n ! * k ^ k := h2
        _ ≤ D * B ^ n * k ^ k := Nat.mul_le_mul_right _ hn
    have h4 : 2 ^ n ≤ D * k ^ k := by
      have h5 : 2 ^ n * B ^ n ≤ D * k ^ k * B ^ n := by
        calc 2 ^ n * B ^ n ≤ D * B ^ n * k ^ k := h3
          _ = D * k ^ k * B ^ n := by ring
      exact Nat.le_of_mul_le_mul_right h5 (pow_pos hB n)
    exact le_trans (le_of_lt Nat.lt_two_pow_self) h4

/-! ### A conditional reduction: `abc` implies finiteness -/

/-- The `ε = 1/2` case of the **abc conjecture**, in an integral form: there is a constant
`C` with `c ^ 2 ≤ C * rad (a * b * c) ^ 3` for all coprime positive `a, b` with `a + b = c`
(equivalently, `c ≤ √C * rad (a * b * c) ^ (3/2)`). -/
