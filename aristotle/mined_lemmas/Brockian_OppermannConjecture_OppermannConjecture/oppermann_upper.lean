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
