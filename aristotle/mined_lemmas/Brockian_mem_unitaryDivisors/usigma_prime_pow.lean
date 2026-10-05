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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  have hp1 : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hdvd, -, hcop⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left; simp
      · right
        by_contra hne
        have hik : i < k := lt_of_le_of_ne hi (by rintro rfl; exact hne rfl)
        rw [Nat.pow_div hi hp.pos] at hcop
        have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
        have h2 : p ∣ p ^ (k - i) := dvd_pow_self p (by omega)
        have hdd := Nat.dvd_gcd h1 h2
        rw [hcop] at hdd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hdd)
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, by positivity, by simp⟩
      · exact ⟨dvd_rfl, by positivity, by simp [Nat.div_self (by positivity : 0 < p ^ k)]⟩
  rw [usigma, hset, Finset.sum_insert (by simp; omega), Finset.sum_singleton, add_comm]

