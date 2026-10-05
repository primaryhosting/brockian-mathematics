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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

/-- **Oppermann's conjecture** (open): for every `n ≥ 2` there is a prime strictly between
`n²` and `n² + n`, and a prime strictly between `n² + n` and `(n+1)²`. -/

lemma next_prime_close (hOpp : Oppermann) {p : ℕ} (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ p < q ∧ q < p + 2 * Nat.sqrt p + 1 := by
  rcases lt_or_ge p 5 with hsmall | hbig
  · -- `p = 2` or `p = 3`
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact absurd hp (by norm_num)
  · obtain ⟨m, hmdef⟩ : ∃ m, Nat.sqrt p = m := ⟨_, rfl⟩
    have hmm : m * m ≤ p := by
      have h := Nat.sqrt_le' p
      rw [hmdef] at h
      simpa [pow_two] using h
    have hlt : p < (m + 1) * (m + 1) := by
      have h := Nat.lt_succ_sqrt' p
      rw [hmdef] at h
      simpa [pow_two] using h
    have hm2 : 2 ≤ m := by
      by_contra hcon
      push_neg at hcon
      interval_cases m <;> omega
    have hne : p ≠ m * m := prime_ne_mul hp hm2 (by nlinarith)
    have hgt : m * m < p := lt_of_le_of_ne hmm (Ne.symm hne)
    rw [hmdef]
    rcases lt_or_ge p (m * m + m) with hcase | hcase
    · obtain ⟨q, hq, hq1, hq2⟩ := (hOpp m hm2).2
      exact ⟨q, hq, by omega, by nlinarith⟩
    · have hne2 : p ≠ m * (m + 1) := prime_ne_mul hp hm2 (by nlinarith)
      have hp' : m * m + m + 1 ≤ p := by
        have hx : p ≠ m * m + m := by
          intro h; exact hne2 (by rw [h]; ring)
        omega
      obtain ⟨q, hq, hq1, hq2⟩ := (hOpp (m + 1) (by omega)).1
      exact ⟨q, hq, by nlinarith, by nlinarith⟩

/-- Any prime greater than the `n`-th prime is at least the `(n+1)`-st prime. -/
