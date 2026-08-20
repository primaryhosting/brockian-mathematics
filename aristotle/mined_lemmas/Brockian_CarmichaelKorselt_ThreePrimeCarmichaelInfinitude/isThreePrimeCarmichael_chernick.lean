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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1`
for every prime `p` dividing `n`. -/

theorem isThreePrimeCarmichael_chernick {k : ℕ} (hk : 1 ≤ k)
    (h1 : Nat.Prime (6 * k + 1)) (h2 : Nat.Prime (12 * k + 1))
    (h3 : Nat.Prime (18 * k + 1)) :
    IsThreePrimeCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
  set p := 6 * k + 1 with hp
  set q := 12 * k + 1 with hq
  set r := 18 * k + 1 with hr
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hpr : p < r := by omega
  -- the key arithmetic identity
  have hval : p * q * r = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k + 1 := by
    simp only [hp, hq, hr]; ring
  have hcube : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hn1 : 1 < p * q * r := by rw [hval]; omega
  have hsub : p * q * r - 1 = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by
    rw [hval]; ring_nf; omega
  refine ⟨⟨hn1, ?_, ?_, ?_⟩, p, q, r, h1, h2, h3, hpq, hqr, rfl⟩
  · -- not prime
    intro hprime
    have hdvd : p ∣ p * q * r := ⟨q * r, by ring⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
    · exact h1.one_lt.ne' h
    · nlinarith [h1.two_le, h2.two_le, h3.two_le]
  · -- squarefree
    have hcpq : Nat.Coprime p q :=
      (Nat.coprime_primes h1 h2).2 hpq.ne
    have hcpr : Nat.Coprime p r :=
      (Nat.coprime_primes h1 h3).2 hpr.ne
    have hcqr : Nat.Coprime q r :=
      (Nat.coprime_primes h2 h3).2 hqr.ne
    rw [Nat.squarefree_mul_iff]
    refine ⟨Nat.Coprime.mul_left hcpr hcqr, ?_, h3.squarefree⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcpq, h1.squarefree, h2.squarefree⟩
  · -- Korselt divisibility
    intro s hs hsdvd
    have hcases : s = p ∨ s = q ∨ s = r := by
      rcases (Nat.Prime.dvd_mul hs).1 hsdvd with h | h
      · rcases (Nat.Prime.dvd_mul hs).1 h with h' | h'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs h1).1 h')
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hs h2).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hs h3).1 h))
    rw [hsub]
    rcases hcases with h | h | h
    · have hs1 : s - 1 = 6 * k := by omega
      rw [hs1]
      exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
    · have hs1 : s - 1 = 12 * k := by omega
      rw [hs1]
      exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
    · have hs1 : s - 1 = 18 * k := by omega
      rw [hs1]
      exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- The smallest Chernick number, `1729 = 7 * 13 * 19`, is a three-prime Carmichael number. -/
