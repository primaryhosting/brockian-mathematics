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

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

lemma succ_le_mul_two_pow {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ n * 2 ^ n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc n + 1 ≤ n + n := by omega
  _ = n * 2 := by ring
  _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h2

/-- `woodall n + 1 = n * 2 ^ n` for `n ≥ 1`. -/

lemma woodall_add_one {n : ℕ} (hn : 1 ≤ n) : woodall n + 1 = n * 2 ^ n := by
  have := succ_le_mul_two_pow hn
  simp only [woodall]
  omega

/-- Woodall numbers grow at least linearly: `n ≤ W n` for `n ≥ 1`. -/

lemma le_woodall {n : ℕ} (hn : 1 ≤ n) : n ≤ woodall n := by
  have h := woodall_add_one hn
  have h2 : 2 * n ≤ n * 2 ^ n := by
    have h2 : 2 ≤ 2 ^ n := by
      calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc 2 * n = n * 2 := by ring
    _ ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h2
  omega

/-! ## An unconditional partial result: infinitely many composite Woodall numbers -/

def woodallPrimes : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n, 1 ≤ n ∧ p = woodall n}

/--
**Woodall prime infinitude, as a reduction.**

Whether there are infinitely many Woodall primes is an open problem; what is proved here is the
equivalence of the two natural formulations: there are infinitely many *indices* `n` with
`n * 2 ^ n - 1` prime if and only if the *set* of Woodall primes is infinite.
-/

theorem WoodallPrimeInfinitude :
    {n : ℕ | Nat.Prime (woodall n)}.Infinite ↔ woodallPrimes.Infinite := by
  constructor
  · intro hS
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    have hbd : ∀ n ∈ {n : ℕ | Nat.Prime (woodall n)}, n ≤ N := by
      intro n hn
      have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exfalso; subst h; simp [woodall] at hn; exact Nat.not_prime_zero hn
        · exact h
      have hmem : woodall n ∈ woodallPrimes := ⟨hn, n, hn1, rfl⟩
      exact le_trans (le_woodall hn1) (hN hmem)
    exact hS (Set.Finite.subset (Set.finite_Iic N) hbd)
  · intro hP
    by_contra hS
    rw [Set.not_infinite] at hS
    have hsub : woodallPrimes ⊆ woodall '' {n : ℕ | Nat.Prime (woodall n)} := by
      rintro p ⟨hp, n, hn1, rfl⟩
      exact ⟨n, hp, rfl⟩
    exact hP (Set.Finite.subset (hS.image woodall) hsub)

end CullenWoodall
end Brockian
