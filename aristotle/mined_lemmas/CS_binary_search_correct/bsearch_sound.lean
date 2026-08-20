/-
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Binary search for the key `k` in the half-open index range `[lo, hi)` of the
indexed collection `f`. Returns `some i` for an index `i` with `f i = k`, or `none`. -/

theorem bsearch_sound (f : ℕ → α) (k : α) (lo hi : ℕ) :
    ∀ i, bsearch f k lo hi = some i → lo ≤ i ∧ i < hi ∧ f i = k := by
  fun_induction bsearch f k lo hi with
  | case1 lo hi h mid hlt ih =>
      intro i hi'
      have hres := ih i hi'
      exact ⟨by omega, by omega, hres.2.2⟩
  | case2 lo hi h mid hlt hgt ih =>
      intro i hi'
      have hres := ih i hi'
      exact ⟨hres.1, by omega, hres.2.2⟩
  | case3 lo hi h mid hlt hgt =>
      intro i hi'
      simp only [Option.some.injEq] at hi'
      subst hi'
      exact ⟨by omega, by omega, le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)⟩
  | case4 lo hi h =>
      intro i hi'
      simp at hi'

/-- Completeness: if the collection is sorted up to index `n` and the key occurs at
some index of the searched range `[lo, hi) ⊆ [0, n)`, then `bsearch` returns an index. -/
