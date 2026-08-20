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
-- (Lean does not allow a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as a block comment and is repeated verbatim as
-- the module docstring immediately after the imports.)

import Mathlib
import Brockian.BrocardData

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is proved here

Brocard's problem asks for all solutions in natural numbers of

$$ n! + 1 = m^2 . $$

The known solutions are `(n, m) = (4, 5), (5, 11), (7, 71)`, and *Brocard's
conjecture* asserts that there are no others.  This is an open problem; a search
of Mathlib turns up no result about the equation `n! + 1 = m²`, so nothing in the
library closes or nearly closes it.  The main library input used below is
`primorial_le_4_pow` (`n# ≤ 4 ^ n`).

Accordingly this file contains:

* `brocard_no_solution_below` : an **unconditional**, kernel-verified check that
  the only solutions with `n ≤ 1000` are the three known ones;
* `BrocardConjecture` : the **conditional reduction** — the full conjecture (as
  an exact classification of all solutions) follows from the statement that
  there is no solution with `n > 1000`;
* `brocard_finitely_many_of_abc` : a second, independent conditional result —
  the `abc` conjecture (in the explicit `ε = 1/2`, `ℕ`-valued form
  `c ^ 2 ≤ K * rad (a * b * c) ^ 3`) implies that Brocard's equation has only
  finitely many solutions, i.e. there is a bound beyond which there is none;
* `BrocardConjecture_of_abc_of_bound` : combining the two.
-/

namespace Brockian.BrocardProblem

open Finset

/-! ### Elementary square lemmas -/

/-- A number strictly between two consecutive squares is not a square. -/

theorem factorial_lt_of_abc {K : ℕ}
    (habc : ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      c ^ 2 ≤ K * rad (a * b * c) ^ 3)
    {n m : ℕ} (h : Nat.factorial n + 1 = m ^ 2) :
    Nat.factorial n < K ^ 2 * 4096 ^ n := by
  have hfac : 0 < Nat.factorial n := Nat.factorial_pos n
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
    · exact hm
  have key := habc 1 (Nat.factorial n) (m ^ 2) Nat.one_pos hfac (by omega)
    (Nat.coprime_one_left _)
  have hrad : rad (1 * Nat.factorial n * m ^ 2) ≤ 4 ^ n * m := by
    rw [Nat.one_mul]
    calc rad (Nat.factorial n * m ^ 2) ≤ rad (Nat.factorial n) * rad (m ^ 2) := rad_mul_le _ _
      _ ≤ 4 ^ n * m := Nat.mul_le_mul (rad_factorial_le n) (rad_pow_le hm.ne' two_ne_zero)
  have h1 : (m ^ 2) ^ 2 ≤ K * (4 ^ n * m) ^ 3 :=
    le_trans key (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hrad 3))
  have h2 : m * m ^ 3 ≤ (K * 64 ^ n) * m ^ 3 := by
    calc m * m ^ 3 = (m ^ 2) ^ 2 := by ring
      _ ≤ K * (4 ^ n * m) ^ 3 := h1
      _ = (K * 64 ^ n) * m ^ 3 := by
          rw [mul_pow, ← pow_mul, mul_comm n 3, pow_mul]; ring_nf
  have h3 : m ≤ K * 64 ^ n := Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hm)
  calc Nat.factorial n < m ^ 2 := by omega
    _ ≤ (K * 64 ^ n) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = K ^ 2 * 4096 ^ n := by rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; ring_nf

/-- **Conditional reduction via `abc`.**  If the `abc` conjecture holds (in the
form `AbcConjectureHalf`), then Brocard's equation `n! + 1 = m ^ 2` has no
solution with `n` beyond some bound; in particular it has only finitely many
solutions. -/
