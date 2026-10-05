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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.AndricaConjecture

/-!
Andrica's conjecture states that for consecutive primes `pₙ < pₙ₊₁` one has
`√pₙ₊₁ - √pₙ < 1`.  This is an open problem.  What is proved here is a
*conditional reduction*: Andrica's conjecture follows from Oppermann's
conjecture (which is itself open, but is a statement purely about the
distribution of primes in short intervals around squares).
-/

/-- **Oppermann's conjecture**: for every `m ≥ 2` there is a prime strictly between
`m²` and `m² + m`, and a prime strictly between `m² + m` and `(m+1)²`.
(Equivalently, in the usual formulation, a prime between `n(n-1)` and `n²` and one
between `n²` and `n(n+1)` for every `n > 1`.) -/

theorem legendre_of_andrica (hA : Andrica) : Legendre := by
  intro n hn
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · subst hn1
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩
  · -- `n ≥ 2`
    have hn2' : 2 ≤ n := hn2
    set N := n * n with hN
    have hN4 : 4 ≤ N := by nlinarith
    set k := Nat.count Nat.Prime (N + 1) with hk
    have hk0 : k ≠ 0 := by
      intro h0
      rw [hk, Nat.count_eq_zero ⟨2, Nat.prime_two⟩] at h0
      have h2 : Nat.nth Nat.Prime 0 = 2 := by simp
      omega
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    -- `p` is the largest prime `≤ N`, `q` the smallest prime `> N`
    set p := Nat.nth Nat.Prime j with hp
    set q := Nat.nth Nat.Prime k with hq
    have hpN : p ≤ N := by
      have : Nat.nth Nat.Prime j < N + 1 := Nat.nth_lt_of_lt_count (by omega)
      omega
    have hqmem : q.Prime ∧ N + 1 ≤ q := by
      have hsInf : q = sInf {i : ℕ | Nat.Prime i ∧ N + 1 ≤ i} := by
        rw [hq, hk, Nat.nth_count_eq_sInf]
      have hne : {i : ℕ | Nat.Prime i ∧ N + 1 ≤ i}.Nonempty := by
        obtain ⟨r, hr1, hr2⟩ := Nat.exists_infinite_primes (N + 1)
        exact ⟨r, hr2, hr1⟩
      rw [hsInf]
      exact Nat.sInf_mem hne
    obtain ⟨hqprime, hqN⟩ := hqmem
    refine ⟨q, hqprime, by omega, ?_⟩
    by_contra hcon
    push_neg at hcon
    -- then `√q - √p ≥ (n+1) - n = 1`, contradicting Andrica
    have hA' := hA j
    rw [← hj, ← hp, ← hq] at hA'
    have h1 : Real.sqrt p ≤ (n : ℝ) := by
      have : Real.sqrt p ≤ Real.sqrt ((n : ℝ) * n) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast hpN
      rwa [Real.sqrt_mul_self (Nat.cast_nonneg n)] at this
    have h2 : ((n : ℝ) + 1) ≤ Real.sqrt q := by
      have : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ Real.sqrt q := by
        apply Real.sqrt_le_sqrt
        have : ((n + 1) * (n + 1) : ℕ) ≤ q := hcon
        exact_mod_cast this
      rwa [Real.sqrt_mul_self (by positivity)] at this
    linarith

end Brockian.AndricaConjecture

