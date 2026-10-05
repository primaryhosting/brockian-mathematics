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

lemma gap_le_of_oppermann (hOpp : Oppermann) (n : ℕ) :
    Nat.nth Nat.Prime (n + 1) ≤
      Nat.nth Nat.Prime n + 2 * Nat.sqrt (Nat.nth Nat.Prime n) := by
  set p := Nat.nth Nat.Prime n with hpdef
  set q := Nat.nth Nat.Prime (n + 1) with hqdef
  have hp : p.Prime := Nat.prime_nth_prime n
  have hp2 : 2 ≤ p := hp.two_le
  set k := Nat.sqrt p with hkdef
  have hk1 : k * k ≤ p := by simpa [pow_two] using Nat.sqrt_le' p
  have hk2 : p < (k + 1) * (k + 1) := by simpa [pow_two] using Nat.lt_succ_sqrt' p
  have hkge : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0] at hk2; omega
    · exact hk0
  rcases eq_or_lt_of_le hkge with hk1' | hkge2
  · -- k = 1, so p ∈ {2, 3}
    have hp3 : p ≤ 3 := by nlinarith [hk1', hk2]
    interval_cases p
    · have : q ≤ 3 := nth_prime_succ_le (by norm_num) (by omega)
      omega
    · have : q ≤ 5 := nth_prime_succ_le (by norm_num) (by omega)
      omega
  · -- k ≥ 2
    have hk2' : 2 ≤ k := hkge2
    have hpne : p ≠ k * k := by
      intro hcon
      have hd : k ∣ p := ⟨k, hcon⟩
      rcases Nat.Prime.eq_one_or_self_of_dvd hp k hd with h1 | h1
      · omega
      · nlinarith
    have hpne2 : p ≠ k * k + k := by
      intro hcon
      have hd : k ∣ p := by
        rw [hcon]; exact ⟨k + 1, by ring⟩
      have := (Nat.Prime.eq_one_or_self_of_dvd hp k hd)
      rcases this with h1 | h1
      · omega
      · nlinarith
    rcases lt_or_gt_of_ne hpne2 with hcase | hcase
    · -- p < k² + k : use a prime in (k²+k, (k+1)²)
      obtain ⟨-, r, hr, hr1, hr2⟩ := hOpp k hk2'
      have hqr : q ≤ r := nth_prime_succ_le hr (by omega)
      nlinarith
    · -- p > k² + k : use a prime in ((k+1)², (k+1)² + (k+1))
      obtain ⟨s, hs, hs1, hs2⟩ := (hOpp (k + 1) (by omega)).1
      have hqs : q ≤ s := nth_prime_succ_le hs (by nlinarith)
      nlinarith

/-- **Andrica's conjecture, conditional on Oppermann's conjecture**:
for consecutive primes, `√pₙ₊₁ - √pₙ < 1`. -/
