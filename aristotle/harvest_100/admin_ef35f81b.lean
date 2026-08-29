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

-- (Lean 4 requires `import` lines to precede any module docstring; the header above is repeated
-- as the module docstring immediately below the import.)
import Mathlib

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture** (statement form): for every `n ≥ 2` there is a prime strictly
between `n² - n = n(n-1)` and `n²`, and a prime strictly between `n²` and `n² + n = n(n+1)`. -/
def OppermannStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ p : ℕ, p.Prime ∧ n * n - n < p ∧ p < n * n) ∧
    (∃ q : ℕ, q.Prime ∧ n * n < q ∧ q < n * n + n)

/-- A short-interval prime hypothesis: for every `m ≥ 2` there is a prime `p ≤ m` with
`m - p < √m` (written without square roots as `(m - p)^2 < m`, using truncated subtraction).
Equivalently: every interval `(m - √m, m]` with `m ≥ 2` contains a prime.

This is a well-known strengthening of Legendre's conjecture and is itself open; here it serves as
the hypothesis of a conditional reduction of Oppermann's conjecture. -/
def ShortIntervalPrimeHypothesis : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ p : ℕ, p.Prime ∧ p ≤ m ∧ (m - p) ^ 2 < m

/-- For `n ≥ 2`, `n * n` is not prime. -/
theorem not_prime_sq {n : ℕ} (hn : 2 ≤ n) : ¬ (n * n).Prime :=
  Nat.not_prime_mul (by omega) (by omega)

/-- For `n ≥ 2`, `n * (n + 1)` is not prime. -/
theorem not_prime_mul_succ {n : ℕ} (hn : 2 ≤ n) : ¬ (n * n + n).Prime := by
  have : n * n + n = n * (n + 1) := by ring
  rw [this]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- Lower half of Oppermann's conjecture, from the short-interval prime hypothesis. -/
theorem oppermann_lower (h : ShortIntervalPrimeHypothesis) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n * n - n < p ∧ p < n * n := by
  obtain ⟨p, hp, hple, hlt⟩ := h (n * n) (by nlinarith)
  refine ⟨p, hp, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
    have hd : n ≤ n * n - p := by omega
    have : n * n ≤ (n * n - p) ^ 2 := by nlinarith [Nat.pow_le_pow_left hd 2]
    exact absurd hlt (not_lt.mpr this)
  · rcases lt_or_eq_of_le hple with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hp) (not_prime_sq hn)

/-- Upper half of Oppermann's conjecture, from the short-interval prime hypothesis. -/
theorem oppermann_upper (h : ShortIntervalPrimeHypothesis) {n : ℕ} (hn : 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ n * n < q ∧ q < n * n + n := by
  obtain ⟨p, hp, hple, hlt⟩ := h (n * n + n) (by nlinarith)
  have hge : n * n ≤ p := by
    by_contra hcon
    push_neg at hcon
    have hd : n + 1 ≤ n * n + n - p := by omega
    have : (n + 1) ^ 2 ≤ (n * n + n - p) ^ 2 := Nat.pow_le_pow_left hd 2
    have hexp : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  refine ⟨p, hp, ?_, ?_⟩
  · rcases lt_or_eq_of_le hge with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hp) (not_prime_sq hn)
  · rcases lt_or_eq_of_le hple with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hp) (not_prime_mul_succ hn)

/-- **Conditional reduction of Oppermann's conjecture.**

Oppermann's conjecture is an open problem, so what is proved here is a reduction: assuming the
short-interval prime hypothesis `ShortIntervalPrimeHypothesis` (every interval `(m - √m, m]`,
`m ≥ 2`, contains a prime), Oppermann's conjecture holds — for every `n ≥ 2` there is a prime
strictly between `n(n-1)` and `n²` and a prime strictly between `n²` and `n(n+1)`. -/
theorem OppermannConjecture (h : ShortIntervalPrimeHypothesis) : OppermannStatement :=
  fun _ hn => ⟨oppermann_lower h hn, oppermann_upper h hn⟩

set_option maxRecDepth 40000 in
/-- Unconditional verification of Oppermann's conjecture for all `2 ≤ n ≤ 20`. -/
theorem oppermann_small : ∀ n ∈ Finset.Icc 2 20,
    (∃ p ∈ Finset.Ioo (n * n - n) (n * n), Nat.Prime p) ∧
    (∃ q ∈ Finset.Ioo (n * n) (n * n + n), Nat.Prime q) := by
  decide

/-- Oppermann's conjecture implies Legendre's conjecture: a prime strictly between consecutive
squares. -/
theorem legendre_of_oppermann (h : OppermannStatement) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < (n + 1) * (n + 1) := by
  obtain ⟨-, q, hq, h1, h2⟩ := h n hn
  exact ⟨q, hq, h1, by nlinarith⟩

end Brockian.OppermannConjecture

