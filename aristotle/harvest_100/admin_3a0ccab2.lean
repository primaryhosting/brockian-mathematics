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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture** (statement form): for every `n ≥ 2` there is a prime strictly
between `n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`.

This is an open problem in number theory; it is *not* proved here.  What is proved below
(`OppermannConjecture`) is a conditional reduction: Oppermann's conjecture follows from the
`√x` prime-gap hypothesis `SqrtGapHypothesis`, together with an unconditional finite
verification for `2 ≤ n ≤ 30` (`oppermann_of_le_thirty`).

Mathlib's strongest unconditional result in this direction is Bertrand's postulate,
`Nat.exists_prime_lt_and_le_two_mul`, which gives a prime in `(n, 2n]` and is far too weak to
reach intervals of length `n` around `n²`. -/
def OppermannStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ q : ℕ, q.Prime ∧ n * n < q ∧ q < n * (n + 1))

/-- The `√x` prime-gap hypothesis: for every `m ≥ 2` there is a prime `p` with
`m < p ≤ m + ⌊√m⌋`.  (A strengthening of Legendre's conjecture, itself open.) -/
def SqrtGapHypothesis : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ p : ℕ, p.Prime ∧ m < p ∧ p ≤ m + Nat.sqrt m

/-- `n(n+1)` is not prime for `n ≥ 2`. -/
lemma not_prime_mul_succ {n : ℕ} (hn : 2 ≤ n) : ¬ (n * (n + 1)).Prime := by
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp n ⟨n + 1, rfl⟩) with h | h
  · omega
  · nlinarith [h]

/-- **Conditional Oppermann conjecture.**  Assuming that every interval `(m, m + √m]` with
`m ≥ 2` contains a prime, Oppermann's conjecture holds. -/
theorem OppermannConjecture (H : SqrtGapHypothesis) : OppermannStatement := by
  intro n hn
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  constructor
  · -- a prime in `(n(n-1), n²)`
    set m := n * n - n with hmdef
    have hmul : n * (n - 1) = m := by
      rw [Nat.mul_sub, Nat.mul_one]
    have hsub : m + n = n * n := Nat.sub_add_cancel hnn
    have hm2 : 2 ≤ m := by nlinarith
    obtain ⟨p, hp, hlt, hle⟩ := H m hm2
    have hmlt : m < n ^ 2 := by
      nlinarith
    have hsqrt : Nat.sqrt m < n := Nat.sqrt_lt'.mpr hmlt
    exact ⟨p, hp, by omega, by omega⟩
  · -- a prime in `(n², n(n+1))`
    obtain ⟨q, hq, hlt, hle⟩ := H (n * n) (by nlinarith)
    rw [Nat.sqrt_eq] at hle
    refine ⟨q, hq, hlt, ?_⟩
    rcases lt_or_eq_of_le (show q ≤ n * (n + 1) by rw [Nat.mul_add, Nat.mul_one]; omega) with h | h
    · exact h
    · exact absurd (h ▸ hq) (not_prime_mul_succ hn)

/-- Unconditional finite verification: Oppermann's conjecture holds for all `2 ≤ n ≤ 30`. -/
lemma oppermann_check :
    ∀ n ∈ Finset.Icc 2 30,
      (∃ p ∈ Finset.Ioo (n * (n - 1)) (n * n), Nat.Prime p) ∧
      (∃ q ∈ Finset.Ioo (n * n) (n * (n + 1)), Nat.Prime q) := by
  decide

/-- **Unconditional partial result**: Oppermann's conjecture holds for every `n` with
`2 ≤ n ≤ 30`. -/
theorem oppermann_of_le_thirty (n : ℕ) (h2 : 2 ≤ n) (h30 : n ≤ 30) :
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ q : ℕ, q.Prime ∧ n * n < q ∧ q < n * (n + 1)) := by
  have h := oppermann_check n (Finset.mem_Icc.mpr ⟨h2, h30⟩)
  simp only [Finset.mem_Ioo] at h
  obtain ⟨⟨p, ⟨hp1, hp2⟩, hp⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := h
  exact ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩

end Brockian.OppermannConjecture

