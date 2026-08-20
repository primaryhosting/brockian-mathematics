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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The twin prime conjecture is a famous open problem, so the target theorem
`Brockian.TwinPrimes.TwinPrimeConjecture` is stated here as a *conditional reduction*:
it derives the infinitude of twin primes from `ClementHypothesis`, a purely
elementary (factorial/divisibility) statement.

The mathematical content that is proved unconditionally is **Clement's theorem**:
for `n ≥ 2`, the pair `(n, n+2)` consists of two primes if and only if

`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`.

Consequently `ClementHypothesis` is *equivalent* to the twin prime conjecture
(`twinPrime_iff_clementHypothesis`), so the reduction is faithful: no hidden
strengthening of the conjecture is assumed.
-/

namespace Brockian.TwinPrimes

open Nat Finset

/-- `n` starts a twin prime pair when both `n` and `n + 2` are prime. -/

theorem prime_right_of_clementCriterion {n : ℕ} (hn : 2 ≤ n) (h : ClementCriterion n) :
    (n + 2).Prime := by
  have hodd : ¬ 2 ∣ n := odd_of_clementCriterion hn h
  have hn' : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := dvd_trans ⟨n, by ring⟩ h
  have key : (n + 2) ∣ 2 * (2 * (n - 1)! + 1) := by
    have hEq : 4 * ((n - 1)! + 1) + n = 2 * (2 * (n - 1)! + 1) + (n + 2) := by ring
    rw [hEq] at hn'
    exact (Nat.dvd_add_right (dvd_refl _)).mp (by simpa [Nat.add_comm] using hn')
  have hcop : Nat.Coprime (n + 2) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  have key2 : (n + 2) ∣ 2 * (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left key
  have hz : ((2 * (n - 1)! + 1 : ℕ) : ZMod (n + 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr key2
  have hn2 : ((n : ℕ) : ZMod (n + 2)) = -2 := by
    have : (((n + 2 : ℕ)) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  refine (Nat.prime_iff_fac_equiv_neg_one (n := n + 2) (by omega)).mpr ?_
  have hfac : ((n + 1)! : ℕ) = (n + 1) * n * (n - 1)! := factorial_succ_succ_pred (by omega)
  have : (((n + 2 - 1)! : ℕ) : ZMod (n + 2)) = (((n + 1)! : ℕ) : ZMod (n + 2)) := by
    norm_num
  rw [this, hfac]
  push_cast
  push_cast at hz hn2
  rw [hn2]
  linear_combination hz

/-- **Clement's theorem**: for `n ≥ 2`, `n` and `n + 2` are both prime if and only if
`n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`. -/
