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

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n > 1` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/
def OppermannStatement : Prop :=
  ∀ n : ℕ, 1 < n →
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * (n + 1))

/-- The (open) *square-root prime gap hypothesis*: for every `N ≥ 118` there is a prime
strictly between `N` and `N + √N`.  The threshold `118` is needed: the statement fails for
every `N` with `113 ≤ N ≤ 117`, since the next prime after `113` is `127` while
`117 + ⌊√117⌋ = 127`.  It is conjectured (but not known) that no further exceptions occur. -/
def SqrtGapHypothesis : Prop :=
  ∀ N : ℕ, 118 ≤ N → ∃ p : ℕ, p.Prime ∧ N < p ∧ p < N + Nat.sqrt N

/-- `⌊√(n(n-1))⌋ = n - 1` for `n ≥ 1`. -/
lemma sqrt_mul_pred (n : ℕ) (hn : 1 ≤ n) : Nat.sqrt (n * (n - 1)) = n - 1 := by
  have hlt : Nat.sqrt (n * (n - 1)) < n := by
    rw [Nat.sqrt_lt]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hge : n - 1 ≤ Nat.sqrt (n * (n - 1)) := by
    rw [Nat.le_sqrt]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- Oppermann's conjecture verified directly for `2 ≤ n ≤ 11`. -/
lemma oppermann_small (n : ℕ) (h2 : 1 < n) (h11 : n ≤ 11) :
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * (n + 1)) := by
  interval_cases n
  · exact ⟨⟨3, by norm_num, by norm_num, by norm_num⟩,
           ⟨5, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7, by norm_num, by norm_num, by norm_num⟩,
           ⟨11, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13, by norm_num, by norm_num, by norm_num⟩,
           ⟨17, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨23, by norm_num, by norm_num, by norm_num⟩,
           ⟨29, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨31, by norm_num, by norm_num, by norm_num⟩,
           ⟨37, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨43, by norm_num, by norm_num, by norm_num⟩,
           ⟨53, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨59, by norm_num, by norm_num, by norm_num⟩,
           ⟨67, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨73, by norm_num, by norm_num, by norm_num⟩,
           ⟨83, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨97, by norm_num, by norm_num, by norm_num⟩,
           ⟨101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨113, by norm_num, by norm_num, by norm_num⟩,
           ⟨127, by norm_num, by norm_num, by norm_num⟩⟩

/-- Under the square-root prime gap hypothesis, there is a prime in `(n(n-1), n²)`
for every `n ≥ 12`. -/
lemma lower_interval_of_sqrtGap (H : SqrtGapHypothesis) (n : ℕ) (hn : 12 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n := by
  have hkey : n * (n - 1) + (n - 1) = n * n - 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ n)
    have h1 : 1 + k - 1 = k := by omega
    have h2 : (1 + k) * (1 + k) = (1 + k) * k + k + 1 := by ring
    rw [h1]
    omega
  obtain ⟨p, hp, hlt, hub⟩ := H (n * (n - 1)) (by
    have : 12 * 11 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega)
  refine ⟨p, hp, hlt, ?_⟩
  rw [sqrt_mul_pred n (by omega)] at hub
  have hpos : 0 < n * n := Nat.mul_pos (by omega) (by omega)
  omega

/-- Under the square-root prime gap hypothesis, there is a prime in `(n², n(n+1))`
for every `n ≥ 12`. -/
lemma upper_interval_of_sqrtGap (H : SqrtGapHypothesis) (n : ℕ) (hn : 12 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * (n + 1) := by
  obtain ⟨p, hp, hlt, hub⟩ := H (n * n) (by
    have : 12 * 12 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    omega)
  refine ⟨p, hp, hlt, ?_⟩
  rw [Nat.sqrt_eq] at hub
  have : n * (n + 1) = n * n + n := by ring
  omega

/-- **Conditional proof of Oppermann's conjecture.**  Assuming the square-root prime gap
hypothesis (a prime in `(N, N + √N)` for every `N ≥ 118`), Oppermann's conjecture holds:
for every `n > 1` there is a prime strictly between `n(n-1)` and `n²`, and one strictly
between `n²` and `n(n+1)`.  The finitely many remaining cases `2 ≤ n ≤ 11` are verified
directly. -/
theorem OppermannConjecture (H : SqrtGapHypothesis) : OppermannStatement := by
  intro n hn
  by_cases h : n ≤ 11
  · exact oppermann_small n hn h
  · exact ⟨lower_interval_of_sqrtGap H n (by omega), upper_interval_of_sqrtGap H n (by omega)⟩

/-- Oppermann's conjecture implies **Legendre's conjecture**: for every `k ≥ 1` there is a
prime strictly between `k²` and `(k+1)²`. -/
theorem legendre_of_oppermann (h : OppermannStatement) (k : ℕ) (hk : 1 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ k * k < p ∧ p < (k + 1) * (k + 1) := by
  rcases eq_or_lt_of_le hk with h1 | h1
  · subst h1
    exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨-, p, hp, hlt, hub⟩ := h k h1
    exact ⟨p, hp, hlt, by nlinarith⟩

end Brockian.OppermannConjecture

