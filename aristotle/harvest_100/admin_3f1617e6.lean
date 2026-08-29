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

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`, `prime 1 = 3`, ...). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The statement of Andrica's conjecture: for consecutive primes `pₙ` and `pₙ₊₁`,
`√pₙ₊₁ - √pₙ < 1`. -/
def AndricaStatement : Prop :=
  ∀ n : ℕ, Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1

/-- Oppermann's conjecture: for every `m ≥ 2` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/
def OppermannConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∃ q, Nat.Prime q ∧ m * m - m < q ∧ q < m * m) ∧
    (∃ q, Nat.Prime q ∧ m * m < q ∧ q < m * m + m)

/-! ## Basic facts about the enumeration of primes -/

theorem prime_prime (n : ℕ) : Nat.Prime (prime n) := Nat.prime_nth_prime n

theorem prime_zero : prime 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  rwa [show Nat.count Nat.Prime 2 = 0 from by decide] at h

theorem prime_one : prime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rwa [show Nat.count Nat.Prime 3 = 1 from by decide] at h

theorem prime_two : prime 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 5) (by norm_num)
  rwa [show Nat.count Nat.Prime 5 = 2 from by decide] at h

theorem prime_strictMono : StrictMono prime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- `prime (n+1)` is the least prime exceeding `prime n`. -/
theorem prime_succ_le {n q : ℕ} (hq : Nat.Prime q) (h : prime n < q) : prime (n + 1) ≤ q := by
  simp only [prime] at h ⊢
  by_contra hc
  push_neg at hc
  exact absurd (Nat.le_nth_of_lt_nth_succ hc hq) (by omega)

theorem five_le_prime {n : ℕ} (hn : 2 ≤ n) : 5 ≤ prime n := by
  have := prime_strictMono.monotone hn
  rwa [prime_two] at this

/-! ## The reformulation of Andrica's inequality -/

/-- Andrica's inequality `√y - √x < 1` is equivalent to the "gap" inequality
`y < x + 2√x + 1`. This is the standard reformulation of the conjecture. -/
theorem sqrt_sub_sqrt_lt_one_iff {x y : ℝ} (hx : 0 ≤ x) :
    Real.sqrt y - Real.sqrt x < 1 ↔ y < x + 2 * Real.sqrt x + 1 := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  constructor
  · intro h
    have h1 : Real.sqrt y < Real.sqrt x + 1 := by linarith
    have h2 := (Real.sqrt_lt' (x := y) (y := Real.sqrt x + 1) (by linarith)).1 h1
    nlinarith
  · intro h
    have h2 : y < (Real.sqrt x + 1) ^ 2 := by nlinarith
    have := (Real.sqrt_lt' (x := y) (y := Real.sqrt x + 1) (by linarith)).2 h2
    linarith

/-- Unconditional criterion: Andrica's inequality holds at `n` as soon as *some* prime `q`
lies in the interval `(pₙ, pₙ + 2√pₙ + 1)`. -/
theorem andrica_of_exists_prime {n q : ℕ} (hq : Nat.Prime q) (hlt : prime n < q)
    (hbound : (q : ℝ) < (prime n : ℝ) + 2 * Real.sqrt (prime n) + 1) :
    Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := by
  have hle : (prime (n + 1) : ℝ) ≤ (q : ℝ) := Nat.cast_le.2 (prime_succ_le hq hlt)
  exact (sqrt_sub_sqrt_lt_one_iff (by positivity)).2 (by linarith)

/-! ## Oppermann's conjecture implies the prime-gap bound -/

/-- Under Oppermann's conjecture, consecutive primes satisfy `pₙ₊₁ < pₙ + 2√pₙ + 1`. -/
theorem gap_bound_of_oppermann (hOpp : OppermannConjecture) {n : ℕ} (hn : 2 ≤ n) :
    (prime (n + 1) : ℝ) < (prime n : ℝ) + 2 * Real.sqrt (prime n) + 1 := by
  set a := prime n with ha
  set b := prime (n + 1) with hb
  set k := Nat.sqrt a with hk
  have ha5 : 5 ≤ a := five_le_prime hn
  have hk2 : 2 ≤ k := Nat.le_sqrt.2 (by omega)
  have hkk : k * k ≤ a := Nat.sqrt_le a
  have hka : a < (k + 1) * (k + 1) := Nat.lt_succ_sqrt a
  have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  have hkR : (k : ℝ) ≤ Real.sqrt a := by
    rw [show ((k : ℝ)) = Real.sqrt ((k : ℝ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : ((k * k : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.2 hkk
    push_cast at this ⊢
    nlinarith
  obtain ⟨⟨q1, hq1p, hq1l, hq1r⟩, ⟨q2, hq2p, hq2l, hq2r⟩⟩ := hOpp (k + 1) (by omega)
  rcases Nat.lt_or_ge a (k * k + k + 1) with hcase | hcase
  · -- Case A : `a ≤ k² + k`; use the prime in `((k+1)² - (k+1), (k+1)²)`
    have hle : b ≤ q1 := prime_succ_le hq1p (by omega)
    have hbnat : b ≤ a + 2 * k := by omega
    have hbR : (b : ℝ) ≤ (a : ℝ) + 2 * (k : ℝ) := by exact_mod_cast Nat.cast_le.2 hbnat
    linarith
  · -- Case B : `a ≥ k² + k + 1`; use the prime in `((k+1)², (k+1)² + (k+1))`
    have hle : b ≤ q2 := prime_succ_le hq2p (by omega)
    have hbnat : b ≤ k * k + 3 * k + 1 := by omega
    have haR : (k : ℝ) * (k : ℝ) + (k : ℝ) + 1 ≤ (a : ℝ) := by
      have : ((k * k + k + 1 : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.2 (by omega)
      push_cast at this
      linarith
    have hsqrt : (k : ℝ) + 1 / 2 < Real.sqrt a :=
      (Real.lt_sqrt (by positivity)).2 (by nlinarith)
    have hbR : (b : ℝ) ≤ (k : ℝ) * (k : ℝ) + 3 * (k : ℝ) + 1 := by
      have : ((b : ℕ) : ℝ) ≤ ((k * k + 3 * k + 1 : ℕ) : ℝ) := Nat.cast_le.2 hbnat
      push_cast at this
      linarith
    linarith

/-! ## Main result -/

/-- **Andrica's conjecture**, conditional on Oppermann's conjecture: for all `n`,
`√pₙ₊₁ - √pₙ < 1`, where `pₙ` denotes the `n`-th prime.

Andrica's conjecture is a well-known open problem; what is established here is the
unconditional implication `Oppermann ⟹ Andrica`, together with the unconditional
verification of the first two cases. -/
theorem AndricaConjecture (hOpp : OppermannConjecture) : AndricaStatement := by
  intro n
  match n with
  | 0 =>
    rw [prime_zero, prime_one, sqrt_sub_sqrt_lt_one_iff (by positivity)]
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    push_cast
    linarith
  | 1 =>
    rw [prime_one, prime_two, sqrt_sub_sqrt_lt_one_iff (by positivity)]
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    push_cast
    linarith
  | (m + 2) =>
    have hgap := gap_bound_of_oppermann hOpp (n := m + 2) (by omega)
    exact (sqrt_sub_sqrt_lt_one_iff (x := (prime (m + 2) : ℝ)) (y := (prime (m + 3) : ℝ))
      (by positivity)).2 (by exact_mod_cast hgap)

end Brockian.AndricaConjecture

