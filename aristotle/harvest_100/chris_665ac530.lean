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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude

A *Woodall number* is `W n = n * 2 ^ n - 1`, and a *Woodall prime* is a Woodall
number that is prime.  Whether there are infinitely many Woodall primes is an
open problem, so the target theorem `WoodallPrimeInfinitude` is stated as a
*reduction*: it lists three reformulations of the conjecture and proves them
equivalent (a `TFAE` statement).  Unconditional partial results (explicit
Woodall primes, and basic structural facts) are proved as well.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- `n` is a *Woodall prime index* when the `n`-th Woodall number is prime. -/
def IsWoodallPrime (n : ℕ) : Prop := Nat.Prime (woodall n)

/-- The set of Woodall primes, i.e. primes of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def woodallPrimes : Set ℕ := {p | p.Prime ∧ ∃ n, 0 < n ∧ p = woodall n}

@[simp] theorem woodall_one : woodall 1 = 1 := rfl
@[simp] theorem woodall_two : woodall 2 = 7 := rfl
@[simp] theorem woodall_three : woodall 3 = 23 := rfl
@[simp] theorem woodall_six : woodall 6 = 383 := rfl

/-- Woodall numbers are (weakly) monotone in the index. -/
theorem woodall_mono : Monotone woodall := by
  intro m n hmn
  have h : m * 2 ^ m ≤ n * 2 ^ n :=
    Nat.mul_le_mul hmn (Nat.pow_le_pow_right (by norm_num) hmn)
  exact Nat.sub_le_sub_right h 1

/-- On positive indices, Woodall numbers are strictly increasing. -/
theorem woodall_lt_woodall {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    woodall m < woodall n := by
  have h2 : m * 2 ^ m < n * 2 ^ m := by
    exact Nat.mul_lt_mul_of_lt_of_le hmn (le_refl _) (Nat.two_pow_pos m)
  have h3 : n * 2 ^ m ≤ n * 2 ^ n :=
    Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by norm_num) hmn.le)
  have h4 : 1 ≤ m * 2 ^ m := Nat.one_le_iff_ne_zero.2 (by positivity)
  unfold woodall
  omega
/-- `woodall` is injective on positive indices. -/
theorem woodall_injOn : Set.InjOn woodall {n : ℕ | 0 < n} := by
  intro m hm n hn h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (woodall_lt_woodall hm hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (woodall_lt_woodall hn hgt))

/-- Every index is bounded by its Woodall number (for positive indices). -/
theorem le_woodall {n : ℕ} (hn : 0 < n) : n ≤ woodall n := by
  have h : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : n * 2 ≤ n * 2 ^ n := Nat.mul_le_mul_left n h
  unfold woodall
  omega

/-- **Target theorem (conditional reduction).**  The Woodall prime infinitude
conjecture — currently open — is equivalent to each of the following:

1. there are arbitrarily large indices `n` with `n * 2 ^ n - 1` prime;
2. the set of such indices is infinite;
3. the set of Woodall primes is infinite.

This theorem proves these three formulations equivalent; it does not decide
whether they hold. -/
theorem WoodallPrimeInfinitude :
    [ ∀ N : ℕ, ∃ n, N < n ∧ IsWoodallPrime n,
      {n : ℕ | 0 < n ∧ IsWoodallPrime n}.Infinite,
      woodallPrimes.Infinite ].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro a
    obtain ⟨n, hn, hp⟩ := h a
    exact ⟨n, ⟨by omega, hp⟩, hn⟩
  tfae_have 2 → 3 := by
    intro h
    have hsub : woodall '' {n : ℕ | 0 < n ∧ IsWoodallPrime n} ⊆ woodallPrimes := by
      rintro p ⟨n, ⟨hn, hp⟩, rfl⟩
      exact ⟨hp, n, hn, rfl⟩
    refine Set.Infinite.mono hsub ?_
    exact Set.Infinite.image (fun m hm n hn hmn =>
      woodall_injOn hm.1 hn.1 hmn) h
  tfae_have 3 → 1 := by
    intro h N
    obtain ⟨p, ⟨hp, n, hn, rfl⟩, hgt⟩ := h.exists_gt (woodall (N + 1))
    refine ⟨n, ?_, hp⟩
    by_contra hle
    exact absurd (woodall_mono (show n ≤ N + 1 by omega)) (by omega)
  tfae_finish

/-- Contrapositive form of the conjecture: the Woodall primes are finite exactly
when all sufficiently large indices give composite Woodall numbers. -/
theorem woodallPrimes_finite_iff :
    ¬ woodallPrimes.Infinite ↔ ∃ N : ℕ, ∀ n, N < n → ¬ IsWoodallPrime n := by
  have h := (WoodallPrimeInfinitude.out 0 2)
  rw [← h]
  push_neg
  tauto

/-! ### Unconditional partial results -/

/-- Every Woodall number with positive index is odd; in particular `2` is not a
Woodall prime. -/
theorem woodall_odd {n : ℕ} (hn : 0 < n) : Odd (woodall n) := by
  have h : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : 2 ∣ n * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 hn.ne') n
  have hge : 1 * 2 ≤ n * 2 ^ n := Nat.mul_le_mul hn h
  refine ⟨k - 1, ?_⟩
  have : 1 ≤ k := by omega
  unfold woodall
  omega

theorem two_notMem_woodallPrimes : (2 : ℕ) ∉ woodallPrimes := by
  rintro ⟨-, n, hn, h⟩
  have := woodall_odd hn
  rw [← h] at this
  simp [Nat.odd_iff] at this

/-- `7 = 2 · 2 ^ 2 - 1` is a Woodall prime. -/
theorem seven_mem_woodallPrimes : (7 : ℕ) ∈ woodallPrimes :=
  ⟨by norm_num, 2, by norm_num, by norm_num⟩

/-- `23 = 3 · 2 ^ 3 - 1` is a Woodall prime. -/
theorem twentyThree_mem_woodallPrimes : (23 : ℕ) ∈ woodallPrimes :=
  ⟨by norm_num, 3, by norm_num, by norm_num⟩

/-- `383 = 6 · 2 ^ 6 - 1` is a Woodall prime. -/
theorem threeEightyThree_mem_woodallPrimes : (383 : ℕ) ∈ woodallPrimes :=
  ⟨by norm_num, 6, by norm_num, by norm_num⟩

/-- Three explicit Woodall primes. -/
theorem triple_subset_woodallPrimes : ({7, 23, 383} : Set ℕ) ⊆ woodallPrimes := by
  rintro x (rfl | rfl | rfl)
  · exact seven_mem_woodallPrimes
  · exact twentyThree_mem_woodallPrimes
  · exact threeEightyThree_mem_woodallPrimes

/-- Unconditionally, there are at least three Woodall primes. -/
theorem three_le_woodallPrimes_ncard (h : woodallPrimes.Finite) :
    3 ≤ woodallPrimes.ncard := by
  have hc : ({7, 23, 383} : Set ℕ).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by norm_num), Set.ncard_insert_of_notMem (by norm_num),
      Set.ncard_singleton]
  calc 3 = ({7, 23, 383} : Set ℕ).ncard := hc.symm
  _ ≤ woodallPrimes.ncard := Set.ncard_le_ncard triple_subset_woodallPrimes h

end Brockian.CullenWoodall

