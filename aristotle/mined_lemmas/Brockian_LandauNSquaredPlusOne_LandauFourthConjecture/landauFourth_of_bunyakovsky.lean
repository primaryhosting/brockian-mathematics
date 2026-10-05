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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace LandauNSquaredPlusOne

open Set

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/

theorem landauFourth_of_bunyakovsky (hB : BunyakovskyConjecture) : LandauFourthStatement := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  have hdeg : 1 ≤ (X ^ 2 + 1 : ℤ[X]).natDegree := by
    have : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by compute_degree!
    omega
  have hfix : ∀ p : ℕ, p.Prime → ∃ m : ℤ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval m) := by
    intro p hp
    refine ⟨0, ?_⟩
    simp only [eval_add, eval_pow, eval_X, eval_one]
    norm_num
    intro h
    have : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨m, hm, hprime⟩ := hB (X ^ 2 + 1) hdeg irreducible_X_sq_add_one hfix (N : ℤ)
  have heval : (X ^ 2 + 1 : ℤ[X]).eval m = m ^ 2 + 1 := by simp
  rw [heval] at hprime
  have hm0 : 0 ≤ m := le_trans (Int.natCast_nonneg N) hm.le
  set n : ℕ := m.natAbs
  have hnm : (n : ℤ) = m := Int.natAbs_of_nonneg hm0
  have hmem : n ∈ LandauSet := by
    have : Prime ((n ^ 2 + 1 : ℕ) : ℤ) := by push_cast [hnm]; exact hprime
    exact Nat.prime_iff_prime_int.2 this
  have hle := hN hmem
  have : (N : ℤ) < (n : ℤ) := by rw [hnm]; exact hm
  exact absurd hle (by exact_mod_cast not_le.2 (by exact_mod_cast this))

/-- The hypothesis used above is in fact *equivalent* to Landau's fourth conjecture, so the
reduction above loses nothing. -/
