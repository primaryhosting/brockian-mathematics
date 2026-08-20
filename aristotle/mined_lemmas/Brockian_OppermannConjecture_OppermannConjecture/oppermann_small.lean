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
