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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- A *Woodall prime* is a prime of the form `n * 2 ^ n - 1` with `n ≥ 1`. -/
def IsWoodallPrime (p : ℕ) : Prop := p.Prime ∧ ∃ n, 1 ≤ n ∧ p = woodall n

@[simp] lemma woodall_def (n : ℕ) : woodall n = n * 2 ^ n - 1 := rfl

lemma one_le_mul_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.2 (by positivity)

/-- Woodall numbers are monotone in the index. -/
lemma woodall_mono {m n : ℕ} (hmn : m ≤ n) : woodall m ≤ woodall n := by
  have h : m * 2 ^ m ≤ n * 2 ^ n :=
    Nat.mul_le_mul hmn (Nat.pow_le_pow_right (by norm_num) hmn)
  simpa [woodall] using Nat.sub_le_sub_right h 1

/-- For `n ≥ 2` the `n`-th Woodall number is at least `n`. -/
lemma le_woodall {n : ℕ} (hn : 2 ≤ n) : n ≤ woodall n := by
  have h4 : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h : n * 4 ≤ n * 2 ^ n := Nat.mul_le_mul_left n h4
  simp only [woodall]
  omega

/-! ### The equivalent index formulation -/

/-- The conjecture "there are infinitely many Woodall primes" is equivalent to the statement
that the set of indices `n` with `n * 2 ^ n - 1` prime is unbounded. -/
theorem woodall_infinitude_iff :
    {p : ℕ | IsWoodallPrime p}.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hlt⟩ := hinf.exists_gt (woodall N)
    obtain ⟨hprime, m, -, rfl⟩ := hp
    refine ⟨m, ?_, hprime⟩
    by_contra hle
    have := woodall_mono (show m ≤ N by omega)
    omega
  · intro h
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro N
    obtain ⟨n, hn, hprime⟩ := h (N + 2)
    refine ⟨woodall n, ⟨hprime, n, by omega, rfl⟩, ?_⟩
    have := le_woodall (n := n) (by omega)
    omega

/-- **Conditional infinitude of Woodall primes.**  If for every bound `N` there is an index
`n > N` for which the Woodall number `n * 2 ^ n - 1` is prime, then there are infinitely many
Woodall primes.  (The hypothesis is exactly the — still open — Woodall prime conjecture, so this
is a Lean-checked reduction of the conjecture to its index formulation, not an unconditional
proof.) -/
theorem WoodallPrimeInfinitude (h : ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime) :
    {p : ℕ | IsWoodallPrime p}.Infinite :=
  woodall_infinitude_iff.2 h

/-! ### Unconditional partial results -/

/-- `7 = 2 * 2 ^ 2 - 1` is a Woodall prime. -/
theorem isWoodallPrime_seven : IsWoodallPrime 7 :=
  ⟨by norm_num, 2, by norm_num, by norm_num [woodall]⟩

/-- `23 = 3 * 2 ^ 3 - 1` is a Woodall prime. -/
theorem isWoodallPrime_twentyThree : IsWoodallPrime 23 :=
  ⟨by norm_num, 3, by norm_num, by norm_num [woodall]⟩

/-- `383 = 6 * 2 ^ 6 - 1` is a Woodall prime. -/
theorem isWoodallPrime_threeHundredEightyThree : IsWoodallPrime 383 :=
  ⟨by norm_num, 6, by norm_num, by norm_num [woodall]⟩

lemma two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · rw [if_pos hk] at ih; rw [if_neg (by omega)]; omega
    · rw [if_neg (by omega)] at ih; rw [if_pos (by omega)]; omega

/-- If `n ≡ 4` or `n ≡ 5 [MOD 6]`, then `3` divides the `n`-th Woodall number. -/
lemma three_dvd_woodall {n : ℕ} (h6 : n % 6 = 4 ∨ n % 6 = 5) : 3 ∣ woodall n := by
  have hpow := two_pow_mod_three n
  have hmul : n * 2 ^ n % 3 = (n % 3) * (2 ^ n % 3) % 3 := by
    rw [Nat.mul_mod]
  have h1 : 1 ≤ n * 2 ^ n := one_le_mul_pow (by omega)
  rcases h6 with h6 | h6
  · have h2 : n % 2 = 0 := by omega
    have h3 : n % 3 = 1 := by omega
    rw [if_pos h2] at hpow
    rw [hpow, h3] at hmul
    simp only [woodall]
    omega
  · have h2 : n % 2 = 1 := by omega
    have h3 : n % 3 = 2 := by omega
    rw [if_neg (by omega)] at hpow
    rw [hpow, h3] at hmul
    simp only [woodall]
    omega

/-- For `n ≥ 4` with `n ≡ 4` or `5 [MOD 6]`, the Woodall number `n * 2 ^ n - 1` is composite. -/
theorem woodall_not_prime {n : ℕ} (hn : 4 ≤ n) (h6 : n % 6 = 4 ∨ n % 6 = 5) :
    ¬ (woodall n).Prime := by
  intro hp
  have hdvd : 3 ∣ woodall n := three_dvd_woodall h6
  have hbig : 3 < woodall n := by
    have h16 : 16 ≤ 2 ^ n := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : n * 16 ≤ n * 2 ^ n := Nat.mul_le_mul_left n h16
    simp only [woodall]
    omega
  rcases (hp.eq_one_or_self_of_dvd 3 hdvd) with h | h <;> omega

/-- There are infinitely many indices `n` for which the Woodall number is composite. -/
theorem infinite_composite_woodall : {n : ℕ | ¬ (woodall n).Prime}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 6 * k + 10)
  · intro a b hab
    simpa using hab
  · intro k
    exact woodall_not_prime (by omega) (Or.inl (by omega))

end Brockian.CullenWoodall

