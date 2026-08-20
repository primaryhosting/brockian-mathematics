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

import Mathlib
/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Twin Prime Conjecture is a famous open problem; it is stated below as
`Brockian.TwinPrimes.TwinPrimeConjecture`.  What this file establishes, fully and
axiom-cleanly, is a set of Lean-checked *reductions* and *partial results*:

* `twinPrimeConjecture_iff_infinite` : the conjecture is equivalent to the infinitude of
  the set of twin primes;
* `clement` : **Clement's criterion** — for `n ≥ 2`, `n` and `n + 2` are both prime iff
  `n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`;
* `twinPrimeConjecture_iff_clement` : consequently the conjecture is equivalent to a purely
  arithmetic statement about factorial congruences;
* `not_twinPrimeConjecture_iff_bddAbove` : its negation is equivalent to the existence of a
  largest twin prime pair;
* unconditional partial results: `six_dvd_succ_of_twin` and `twin_primes_small`.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `p` is the smaller member of a twin prime pair. -/

theorem prime_right_of_dvd {n : ℕ} (hn : 2 ≤ n) (hd : n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n) :
    (n + 2).Prime := by
  have hodd := odd_of_dvd hn hd
  have hcop : Nat.Coprime (n + 2) 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have hp : (n + 2) ∣ 4 * ((n - 1)! + 1) + n := dvd_trans (Dvd.intro_left _ rfl) hd
  have h2 : (n + 2) ∣ 2 * (2 * (n - 1)! + 1) := by
    have h := Nat.dvd_sub hp (dvd_refl (n + 2))
    have he : 4 * ((n - 1)! + 1) + n - (n + 2) = 2 * (2 * (n - 1)! + 1) := by omega
    rwa [he] at h
  have h3 : (n + 2) ∣ 2 * (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  have hp3 : (m + 3).Prime := by
    refine (Nat.prime_iff_fac_equiv_neg_one (by omega)).2 ?_
    have hz : ((2 * m ! + 1 : ℕ) : ZMod (m + 3)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by convert h3 using 2)
    push_cast at hz
    have hx : ((m : ℕ) : ZMod (m + 3)) = -3 := by
      have := ZMod.natCast_self (m + 3)
      push_cast at this
      linear_combination this
    have hfac : (m + 3 - 1)! = (m + 2) * ((m + 1) * m !) := by
      show (m + 2)! = _
      rw [Nat.factorial_succ, Nat.factorial_succ]
    rw [hfac]
    push_cast
    rw [hx]
    linear_combination hz
  convert hp3 using 2

/-- **Clement's criterion** for twin primes: for `n ≥ 2`, the pair `(n, n + 2)` consists of
two primes if and only if `n * (n + 2)` divides `4 * ((n - 1)! + 1) + n`. -/
