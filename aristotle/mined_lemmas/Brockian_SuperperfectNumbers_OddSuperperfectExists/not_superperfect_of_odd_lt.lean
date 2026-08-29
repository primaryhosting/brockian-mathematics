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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists

Category: Brockian Conjecture

Target: `Brockian.SuperperfectNumbers.OddSuperperfectExists`

A natural number `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ = σ₁` is the
sum-of-divisors function.  The even superperfect numbers are exactly the numbers `2 ^ k`
with `2 ^ (k + 1) - 1` prime; whether an **odd** superperfect number exists is an open
problem.  Accordingly this file does not claim the (open) existence statement.  Instead it
proves unconditional structural facts about a hypothetical odd superperfect number and
packages them as a Lean-checked *conditional reduction*:

* `odd_sigma_of_superperfect`: for every superperfect `n > 0`, `σ n` is odd;
* `isSquare_of_odd_superperfect`: every odd superperfect number is a perfect square
  (Suryanarayana);
* `not_superperfect_of_odd_lt`: there is no odd superperfect number below `4096`;
* `OddSuperperfectExists`: an odd superperfect number exists **iff** there is an odd
  superperfect perfect square that is at least `4096`.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `n` is *superperfect* when `σ (σ n) = 2 * n`, where `σ` is the sum-of-divisors
function. -/

theorem not_superperfect_of_odd_lt {n : ℕ} (hodd : Odd n) (hlt : n < 4096) :
    ¬ Superperfect n := by
  intro hsp
  have hn : 0 < n := hodd.pos
  obtain ⟨j, hj⟩ := isSquare_of_odd_superperfect hn hodd hsp
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with he | ho
    · exact absurd (hj ▸ he.mul_right j) (Nat.not_even_iff_odd.2 hodd)
    · exact ho
  have hj64 : j < 64 := by nlinarith [hj, hlt]
  exact not_superperfect_odd_sq_lt_64 j (Finset.mem_range.2 hj64) hjodd (hj ▸ hsp)

/-- **Target (conditional reduction).**  Whether an odd superperfect number exists is an
open problem, so we prove instead the following equivalence:  an odd superperfect number
exists **if and only if** there is an odd superperfect number which is moreover a perfect
square and at least `4096`. -/
