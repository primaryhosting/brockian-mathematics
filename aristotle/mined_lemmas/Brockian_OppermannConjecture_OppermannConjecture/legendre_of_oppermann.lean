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

theorem legendre_of_oppermann (h : OppermannStatement) (k : ℕ) (hk : 1 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ k * k < p ∧ p < (k + 1) * (k + 1) := by
  rcases eq_or_lt_of_le hk with h1 | h1
  · subst h1
    exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨-, p, hp, hlt, hub⟩ := h k h1
    exact ⟨p, hp, hlt, by nlinarith⟩

end Brockian.OppermannConjecture

