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
def Oppermann : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∃ p : ℕ, p.Prime ∧ m * m < p ∧ p < m * m + m) ∧
    (∃ p : ℕ, p.Prime ∧ m * m + m < p ∧ p < (m + 1) * (m + 1))

/-- The `(n+1)`-st prime is at most any prime exceeding the `n`-th prime. -/
lemma nth_prime_succ_le {n q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  by_contra hcon
  push_neg at hcon
  have := Nat.le_nth_of_lt_nth_succ hcon hq
  omega

/-- If `k² ≤ p` and `q ≤ p + 2k`, then `√q - √p < 1`. -/
lemma sqrt_sub_sqrt_lt_one {p q k : ℕ} (hk : k * k ≤ p) (h : q ≤ p + 2 * k) :
    Real.sqrt q - Real.sqrt p < 1 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsk : (k : ℝ) ≤ Real.sqrt p := by
    have : Real.sqrt ((k : ℝ) * k) ≤ Real.sqrt p := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hk
    rwa [Real.sqrt_mul_self (Nat.cast_nonneg k)] at this
  have hsp : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hp0
  have hq : (q : ℝ) ≤ (p : ℝ) + 2 * k := by exact_mod_cast h
  have hlt : (q : ℝ) < (Real.sqrt p + 1) ^ 2 := by nlinarith
  have hspn : (0 : ℝ) ≤ Real.sqrt p + 1 := by positivity
  have : Real.sqrt q < Real.sqrt ((Real.sqrt p + 1) ^ 2) := by
    apply Real.sqrt_lt_sqrt (Nat.cast_nonneg q) hlt
  rw [Real.sqrt_sq hspn] at this
  linarith

/-- Unconditional reformulation of Andrica's inequality as a prime-gap bound:
`√q - √p < 1` holds exactly when `q < p + 2√p + 1`. -/
lemma sqrt_sub_sqrt_lt_one_iff (p q : ℝ) (hp : 0 ≤ p) :
    Real.sqrt q - Real.sqrt p < 1 ↔ q < p + 2 * Real.sqrt p + 1 := by
  have hspn : (0 : ℝ) < 1 + Real.sqrt p := by positivity
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp
  rw [sub_lt_iff_lt_add, Real.sqrt_lt' hspn]
  constructor <;> intro h <;> nlinarith

/-- Under Oppermann's conjecture, the prime gap satisfies `pₙ₊₁ ≤ pₙ + 2⌊√pₙ⌋`. -/
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
theorem AndricaConjecture (hOpp : Oppermann) (n : ℕ) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1 :=
  sqrt_sub_sqrt_lt_one (by simpa [pow_two] using Nat.sqrt_le' (Nat.nth Nat.Prime n))
    (gap_le_of_oppermann hOpp n)

/-- **Andrica's conjecture** as a proposition: `√pₙ₊₁ - √pₙ < 1` for all `n`. -/
def Andrica : Prop :=
  ∀ n : ℕ, Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n) < 1

/-- Oppermann's conjecture implies Andrica's conjecture. -/
theorem andrica_of_oppermann (hOpp : Oppermann) : Andrica :=
  AndricaConjecture hOpp

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between `n²`
and `(n+1)²`. -/
def Legendre : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < (n + 1) * (n + 1)

/-- Andrica's conjecture implies Legendre's conjecture. -/
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

