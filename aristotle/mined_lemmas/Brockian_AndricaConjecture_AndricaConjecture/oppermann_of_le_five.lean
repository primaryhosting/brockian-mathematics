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

lemma oppermann_of_le_five {n : ℕ} (h2 : 2 ≤ n) (h5 : n ≤ 5) :
    (∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * n + n) ∧
    (∃ p : ℕ, p.Prime ∧ n * n + n < p ∧ p < (n + 1) * (n + 1)) := by
  interval_cases n
  · exact ⟨⟨5, by norm_num⟩, ⟨7, by norm_num⟩⟩
  · exact ⟨⟨11, by norm_num⟩, ⟨13, by norm_num⟩⟩
  · exact ⟨⟨17, by norm_num⟩, ⟨23, by norm_num⟩⟩
  · exact ⟨⟨29, by norm_num⟩, ⟨31, by norm_num⟩⟩

/-- If `m² ≤ p` and `q < p + 2m + 1`, then `√q - √p < 1`. -/
