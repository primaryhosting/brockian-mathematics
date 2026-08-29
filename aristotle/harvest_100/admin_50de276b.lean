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
def Oppermann : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * n + n) ∧
    (∃ p : ℕ, p.Prime ∧ n * n + n < p ∧ p < (n + 1) * (n + 1))

/-- Sanity check (non-vacuity): the two Oppermann intervals do contain primes for `2 ≤ n ≤ 5`. -/
lemma oppermann_of_le_five {n : ℕ} (h2 : 2 ≤ n) (h5 : n ≤ 5) :
    (∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * n + n) ∧
    (∃ p : ℕ, p.Prime ∧ n * n + n < p ∧ p < (n + 1) * (n + 1)) := by
  interval_cases n
  · exact ⟨⟨5, by norm_num⟩, ⟨7, by norm_num⟩⟩
  · exact ⟨⟨11, by norm_num⟩, ⟨13, by norm_num⟩⟩
  · exact ⟨⟨17, by norm_num⟩, ⟨23, by norm_num⟩⟩
  · exact ⟨⟨29, by norm_num⟩, ⟨31, by norm_num⟩⟩

/-- If `m² ≤ p` and `q < p + 2m + 1`, then `√q - √p < 1`. -/
lemma sqrt_sub_sqrt_lt_one {p q m : ℕ} (hm : m * m ≤ p) (h : q < p + 2 * m + 1) :
    Real.sqrt q - Real.sqrt p < 1 := by
  have hp0 : (0:ℝ) ≤ (p : ℝ) := by positivity
  have hmp : (m : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0]
    have : ((m * m : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hm
    push_cast at this
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt p + 1 := by positivity
  have hlt : Real.sqrt q < Real.sqrt p + 1 := by
    rw [Real.sqrt_lt' hpos]
    have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0
    have hq : (q : ℝ) < (p : ℝ) + 2 * m + 1 := by exact_mod_cast h
    nlinarith
  linarith

/-- A prime is never of the form `m * k` with `2 ≤ m` and `m < m * k`. -/
lemma prime_ne_mul {p m k : ℕ} (hp : p.Prime) (hm : 2 ≤ m) (hlt : m < m * k) :
    p ≠ m * k := by
  rintro rfl
  rcases hp.eq_one_or_self_of_dvd m ⟨k, rfl⟩ with h | h
  · omega
  · omega

/-- Oppermann's conjecture implies: after every prime `p` there is a prime `q`
with `p < q < p + 2⌊√p⌋ + 1`. -/
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
lemma nth_prime_succ_le {n q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  have hcount : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hlt : n < Nat.count Nat.Prime q := by
    rw [← Nat.nth_lt_nth Nat.infinite_setOf_prime (k := n) (n := Nat.count Nat.Prime q), hcount]
    exact h
  calc Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
    _ = q := hcount

/-- Unconditional criterion: Andrica's inequality holds at `n` as soon as the prime gap
satisfies `pₙ₊₁ < pₙ + 2⌊√pₙ⌋ + 1`. -/
theorem andrica_of_prime_gap {n : ℕ}
    (h : Nat.nth Nat.Prime (n + 1) <
      Nat.nth Nat.Prime n + 2 * Nat.sqrt (Nat.nth Nat.Prime n) + 1) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 :=
  sqrt_sub_sqrt_lt_one (by simpa [pow_two] using Nat.sqrt_le' (Nat.nth Nat.Prime n)) h

/-- Unconditional partial result: Andrica's inequality holds for the first few primes. -/
theorem andrica_of_index_le_three {n : ℕ} (hn : n ≤ 3) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 := by
  interval_cases n
  · rw [show Nat.nth Nat.Prime 0 = 2 by norm_num, show Nat.nth Nat.Prime 1 = 3 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 1) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 1 = 3 by norm_num, show Nat.nth Nat.Prime 2 = 5 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 1) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 2 = 5 by norm_num, show Nat.nth Nat.Prime 3 = 7 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 2) (by norm_num) (by norm_num)
  · rw [show Nat.nth Nat.Prime 3 = 7 by norm_num, show Nat.nth Nat.Prime 4 = 11 by norm_num]
    exact sqrt_sub_sqrt_lt_one (m := 2) (by norm_num) (by norm_num)

/-- **Andrica's conjecture**, conditional on Oppermann's conjecture:
for consecutive primes `pₙ < pₙ₊₁` one has `√pₙ₊₁ - √pₙ < 1`. -/
theorem AndricaConjecture (hOpp : Oppermann) (n : ℕ) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 := by
  obtain ⟨q, hq, hq1, hq2⟩ := next_prime_close hOpp (Nat.prime_nth_prime n)
  have hle : Nat.nth Nat.Prime (n + 1) ≤ q := nth_prime_succ_le hq hq1
  refine sqrt_sub_sqrt_lt_one (p := Nat.nth Nat.Prime n) (q := Nat.nth Nat.Prime (n + 1))
    (m := Nat.sqrt (Nat.nth Nat.Prime n)) ?_ ?_
  · simpa [pow_two] using Nat.sqrt_le' (Nat.nth Nat.Prime n)
  · omega

end Brockian.AndricaConjecture

