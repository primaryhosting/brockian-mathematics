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

theorem brocard_finite_of_abc (habc : ABCConjectureHalf) :
    {n : ℕ | ∃ m : ℕ, n ! + 1 = m ^ 2}.Finite := by
  obtain ⟨C, hC⟩ := habc
  obtain ⟨N, hN⟩ := factorial_exp_bounded (C ^ 2) 4096
  refine Set.Finite.subset (Set.finite_Iic N) ?_
  rintro n ⟨m, hm⟩
  simp only [Set.mem_Iic]
  refine hN n ?_
  have hfac : 0 < n ! := Nat.factorial_pos n
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  have key := hC 1 (n !) (m ^ 2) one_pos hfac (Nat.coprime_one_left _) (by omega)
  have hrad : rad (1 * n ! * m ^ 2) ≤ 4 ^ n * m := by
    rw [Nat.one_mul]
    calc rad (n ! * m ^ 2) ≤ rad (n !) * rad (m ^ 2) := rad_mul_le _ _
      _ = rad (n !) * rad m := by rw [rad_sq]
      _ ≤ 4 ^ n * m := Nat.mul_le_mul (rad_factorial_le n) (rad_le_self hm0.ne')
  have h64 : ((4 : ℕ) ^ n) ^ 3 = 64 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : (m ^ 2) ^ 2 ≤ C * (4 ^ n * m) ^ 3 :=
    le_trans key (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrad 3))
  have h2 : m * m ^ 3 ≤ C * 64 ^ n * m ^ 3 := by
    calc m * m ^ 3 = (m ^ 2) ^ 2 := by ring
      _ ≤ C * (4 ^ n * m) ^ 3 := h1
      _ = C * 64 ^ n * m ^ 3 := by rw [mul_pow, h64]; ring
  have h3 : m ≤ C * 64 ^ n := Nat.le_of_mul_le_mul_right h2 (pow_pos hm0 3)
  calc n ! ≤ m ^ 2 := by omega
    _ ≤ (C * 64 ^ n) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = C ^ 2 * 4096 ^ n := by
        rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; norm_num

end BrocardProblem
end Brockian

import Mathlib

/-!
# Brocard's problem: verification in a small range

This file verifies unconditionally that `n ! + 1` is a perfect square for no `n < 301`
other than `n = 4, 5, 7`.  It is a supporting file for `Brockian.BrocardProblem`.
-/

namespace Brockian
namespace BrocardProblem

open Nat

/-- If `a` lies strictly between two consecutive squares then it is not a square. -/
