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
