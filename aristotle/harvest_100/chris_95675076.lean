import Brockian.CullenWoodall

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
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Mathlib (as of this toolchain) contains no material on Cullen or Woodall numbers -- a search
for `Woodall` returns nothing -- so the notions below are developed from scratch.  The Mathlib
results actually used are `strictMono_nat_of_lt_succ`, `Nat.sub_lt_sub_right`,
`Set.infinite_of_not_bddAbove` and `Set.Infinite.exists_gt`.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; for `n ≥ 1`
this agrees with the usual integer definition). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

lemma woodall_two : woodall 2 = 7 := by decide
lemma woodall_three : woodall 3 = 23 := by decide
lemma woodall_six : woodall 6 = 383 := by decide

lemma woodall_two_prime : Nat.Prime (woodall 2) := by
  rw [woodall_two]; norm_num

lemma woodall_three_prime : Nat.Prime (woodall 3) := by
  rw [woodall_three]; norm_num

lemma woodall_six_prime : Nat.Prime (woodall 6) := by
  rw [woodall_six]; norm_num

/-- The auxiliary map `n ↦ n * 2 ^ n` is strictly monotone. -/
lemma strictMono_mul_two_pow : StrictMono fun n : ℕ => n * 2 ^ n := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
  have h : (n + 1) * 2 ^ (n + 1) = 2 * (n * 2 ^ n) + 2 * 2 ^ n := by ring
  simp only [h]
  nlinarith [h2]

lemma one_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : 1 ≤ n * 2 ^ n :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.two_pow_pos n).ne')

/-- Woodall numbers are strictly increasing from index `1` on. -/
lemma woodall_lt_woodall {m n : ℕ} (hm : 1 ≤ m) (h : m < n) : woodall m < woodall n := by
  have h1 : m * 2 ^ m < n * 2 ^ n := strictMono_mul_two_pow h
  have h2 : 1 ≤ m * 2 ^ m := one_le_mul_two_pow hm
  simpa [woodall] using Nat.sub_lt_sub_right h2 h1

/-- Woodall numbers dominate their index. -/
lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have h : n * 2 ≤ n * 2 ^ n := by
    have h' : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simpa using Nat.mul_le_mul_left n h'
  simp only [woodall]
  omega

/-- The set of Woodall primes. -/
def WoodallPrimes : Set ℕ := {p | Nat.Prime p ∧ ∃ n, 1 ≤ n ∧ woodall n = p}

lemma seven_mem_woodallPrimes : 7 ∈ WoodallPrimes :=
  ⟨by norm_num, 2, by norm_num, woodall_two⟩

/-!
## Main conditional theorem

Whether infinitely many Woodall numbers are prime is an open problem, so we prove the
statement in conditional form: if Woodall primes occur at arbitrarily large indices, then
there are infinitely many Woodall *primes*.  The content of the reduction is that
`n ↦ W n` is strictly increasing for `n ≥ 1` and `W n ≥ n`, so the resulting set of primes
is unbounded.
-/

/-- **Woodall prime infinitude (conditional).**
If for every `N` there is an index `n > N` with `W n = n * 2 ^ n - 1` prime, then the set of
Woodall primes is infinite.  (The unconditional statement is an open problem.) -/
theorem WoodallPrimeInfinitude
    (hW : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n)) :
    WoodallPrimes.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn, hp⟩ := hW B
  have h1 : 1 ≤ n := by omega
  have hmem : woodall n ∈ WoodallPrimes := ⟨hp, n, h1, rfl⟩
  have hle := hB hmem
  have := le_woodall h1
  omega

/-- The converse reduction: infinitely many Woodall primes forces Woodall primes at
arbitrarily large indices. -/
theorem exists_large_index_of_infinite (h : WoodallPrimes.Infinite) :
    ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) := by
  intro N
  obtain ⟨p, hp, hpN⟩ := h.exists_gt (2 ^ (N + 1) * (N + 1))
  obtain ⟨hprime, n, hn, rfl⟩ := hp
  refine ⟨n, ?_, hprime⟩
  by_contra hle
  push_neg at hle
  have hmono : woodall n ≤ woodall (N + 1) :=
    le_of_lt (woodall_lt_woodall hn (Nat.lt_succ_of_le hle))
  have hbd : woodall (N + 1) ≤ 2 ^ (N + 1) * (N + 1) := by
    simp only [woodall]
    calc (N + 1) * 2 ^ (N + 1) - 1 ≤ (N + 1) * 2 ^ (N + 1) := Nat.sub_le _ _
      _ = 2 ^ (N + 1) * (N + 1) := Nat.mul_comm _ _
  omega

/-- The reduction as an equivalence. -/
theorem woodallPrimes_infinite_iff :
    WoodallPrimes.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) :=
  ⟨exists_large_index_of_infinite, WoodallPrimeInfinitude⟩

/-!
## An unconditional partial result

Infinitely many Woodall numbers are composite: for `n ≡ 4 (mod 6)` one has `3 ∣ W n`.
-/

lemma three_dvd_woodall_of (k : ℕ) : 3 ∣ woodall (6 * k + 4) := by
  have hpow : 2 ^ (6 * k + 4) % 3 = 1 := by
    have h1 : (2 : ℕ) ^ (6 * k + 4) = (2 ^ 6) ^ k * 2 ^ 4 := by
      rw [pow_add, pow_mul]
    rw [h1, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hmul : (6 * k + 4) * 2 ^ (6 * k + 4) % 3 = 1 := by
    rw [Nat.mul_mod, hpow]
    omega
  have hge : 1 ≤ (6 * k + 4) * 2 ^ (6 * k + 4) := one_le_mul_two_pow (by omega)
  simp only [woodall]
  omega

lemma woodall_large (k : ℕ) : 63 ≤ woodall (6 * k + 4) := by
  have h : woodall 4 ≤ woodall (6 * k + 4) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact le_of_lt (woodall_lt_woodall (by norm_num) (by omega))
  have h4 : woodall 4 = 63 := by decide
  omega

/-- **Unconditional partial result.** The set of indices at which the Woodall number is
composite is infinite; indeed `3 ∣ W n` whenever `n ≡ 4 (mod 6)`. -/
theorem infinite_composite_woodall :
    {n : ℕ | ¬ Nat.Prime (woodall n)}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hmem : 6 * (B + 1) + 4 ∈ {n : ℕ | ¬ Nat.Prime (woodall n)} := by
    intro hp
    have hdvd := three_dvd_woodall_of (B + 1)
    have hlarge := woodall_large (B + 1)
    have := hp.eq_one_or_self_of_dvd 3 hdvd
    omega
  have := hB hmem
  omega

end Brockian.CullenWoodall

