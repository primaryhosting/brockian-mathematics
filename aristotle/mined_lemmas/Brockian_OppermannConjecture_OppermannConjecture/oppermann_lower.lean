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
