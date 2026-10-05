import Brockian.LandauNSquaredPlusOne

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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/
def LandauPrimes : Set ℕ := {p | Nat.Prime p ∧ ∃ n : ℕ, p = n ^ 2 + 1}

/-- The statement that witnesses `n` with `n ^ 2 + 1` prime occur arbitrarily far out.
This is the standard "unbounded witness" form of Landau's fourth problem. -/
def UnboundedLandauWitnesses : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (n ^ 2 + 1)

/-- **Landau's fourth conjecture (conditional form).**
If witnesses `n` with `n ^ 2 + 1` prime occur arbitrarily far out, then there are infinitely
many primes of the form `n ^ 2 + 1`.  (Landau's fourth problem is open, so the hypothesis is
carried explicitly; the theorem is a Lean-checked reduction of the infinitude statement to the
unbounded-witness statement.) -/
theorem LandauFourthConjecture (h : UnboundedLandauWitnesses) : LandauPrimes.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hp⟩ := h N
  refine ⟨n ^ 2 + 1, ⟨hp, ⟨n, rfl⟩⟩, ?_⟩
  nlinarith

/-- Conversely, infinitude of Landau primes gives back the unbounded-witness statement, so the
two formulations are equivalent. -/
theorem unboundedLandauWitnesses_of_infinite (h : LandauPrimes.Infinite) :
    UnboundedLandauWitnesses := by
  intro N
  obtain ⟨p, hp, hlt⟩ := h.exists_gt ((N + 1) ^ 2 + 1)
  obtain ⟨hpp, n, rfl⟩ := hp
  exact ⟨n, by nlinarith, hpp⟩

/-- Landau's fourth conjecture is equivalent to the unbounded-witness statement. -/
theorem landauFourth_iff : UnboundedLandauWitnesses ↔ LandauPrimes.Infinite :=
  ⟨LandauFourthConjecture, unboundedLandauWitnesses_of_infinite⟩

/-- The set of witnesses: naturals `n` for which `n ^ 2 + 1` is prime. -/
def LandauWitnesses : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- The witness set is infinite exactly when witnesses occur arbitrarily far out. -/
theorem infinite_landauWitnesses_iff : LandauWitnesses.Infinite ↔ UnboundedLandauWitnesses := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hlt, hn⟩ := h N
    exact ⟨n, hn, hlt⟩

/-- Landau's fourth conjecture, in terms of the witness set. -/
theorem infinite_landauWitnesses_iff_infinite_landauPrimes :
    LandauWitnesses.Infinite ↔ LandauPrimes.Infinite :=
  infinite_landauWitnesses_iff.trans landauFourth_iff

/-- Apart from `2 = 1 ^ 2 + 1`, every prime of the form `n ^ 2 + 1` comes from an even, positive
`n`. -/
theorem even_of_landauPrime {p : ℕ} (hp : p ∈ LandauPrimes) (hne : p ≠ 2) :
    ∃ m : ℕ, 0 < m ∧ p = (2 * m) ^ 2 + 1 := by
  obtain ⟨hpp, n, rfl⟩ := hp
  have hn2 : n % 2 = 0 := by
    by_contra hodd
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hdvd : 2 ∣ n ^ 2 + 1 := ⟨2 * k * k + 2 * k + 1, by subst hk; ring⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 hdvd).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at hpp
  refine ⟨n / 2, by omega, ?_⟩
  have h : 2 * (n / 2) = n := by omega
  rw [h]

/-- An odd prime dividing some `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
theorem mod_four_eq_one_of_prime_dvd_sq_add_one {p n : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hdvd : p ∣ n ^ 2 + 1) : p % 4 = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne3 : p % 4 ≠ 3 := by
    have : ((n : ZMod p)) ^ 2 = -1 := by
      have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
      push_cast at h0
      linear_combination h0
    rw [← ZMod.exists_sq_eq_neg_one_iff]
    exact ⟨(n : ZMod p), by rw [← this]; ring⟩
  have h2 : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hodd)
  omega

/-- Unconditionally, infinitely many primes divide some value of `n ^ 2 + 1`. -/
theorem infinite_primes_dvd_sq_add_one :
    {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  apply Set.Infinite.mono (s := {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 4]})
  · rintro p ⟨hp, hmod⟩
    refine ⟨hp, ?_⟩
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hne3 : p % 4 ≠ 3 := by
      have : p % 4 = 1 := hmod
      omega
    obtain ⟨x, hx⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hne3
    refine ⟨x.val, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    linear_combination -hx
  · exact Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num)

/-- Every prime of the form `n ^ 2 + 1` other than `2` is congruent to `1` modulo `4`. -/
theorem landauPrime_mod_four {p : ℕ} (hp : p ∈ LandauPrimes) (hne : p ≠ 2) : p % 4 = 1 := by
  obtain ⟨hpp, n, rfl⟩ := hp
  exact mod_four_eq_one_of_prime_dvd_sq_add_one hpp hne dvd_rfl

/-- Some small Landau primes, checked by decision procedures. -/
theorem sample_landauPrimes :
    ({2, 5, 17, 37, 101, 197, 257, 401} : Set ℕ) ⊆ LandauPrimes := by
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨by norm_num, 1, by norm_num⟩
  · exact ⟨by norm_num, 2, by norm_num⟩
  · exact ⟨by norm_num, 4, by norm_num⟩
  · exact ⟨by norm_num, 6, by norm_num⟩
  · exact ⟨by norm_num, 10, by norm_num⟩
  · exact ⟨by norm_num, 14, by norm_num⟩
  · exact ⟨by norm_num, 16, by norm_num⟩
  · exact ⟨by norm_num, 20, by norm_num⟩

end Brockian.LandauNSquaredPlusOne

