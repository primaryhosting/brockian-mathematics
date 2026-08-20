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

theorem bsearch_complete (f : ℕ → α) (k : α) (n : ℕ)
    (hmono : ∀ i j : ℕ, i ≤ j → j < n → f i ≤ f j) (lo hi : ℕ) (hn : hi ≤ n) :
    ∀ j, lo ≤ j → j < hi → f j = k → (bsearch f k lo hi).isSome := by
  induction lo, hi using bsearch.induct f k with
  | case1 lo hi h mid hlt ih =>
      intro j hj1 hj2 hj3
      rw [bsearch, dif_pos h, if_pos (show f ((lo + hi) / 2) < k from hlt)]
      refine ih (by omega) j ?_ hj2 hj3
      by_contra hcon
      have hle : f j ≤ f mid := hmono j mid (by omega) (by omega)
      rw [hj3] at hle
      exact absurd hlt (not_lt.mpr hle)
  | case2 lo hi h mid hlt hgt ih =>
      intro j hj1 hj2 hj3
      rw [bsearch, dif_pos h, if_neg (show ¬ f ((lo + hi) / 2) < k from hlt),
        if_pos (show k < f ((lo + hi) / 2) from hgt)]
      refine ih (by omega) j hj1 ?_ hj3
      by_contra hcon
      have hle : f mid ≤ f j := hmono mid j (by omega) (by omega)
      rw [hj3] at hle
      exact absurd hgt (not_lt.mpr hle)
  | case3 lo hi h mid hlt hgt =>
      intro j hj1 hj2 hj3
      rw [bsearch, dif_pos h, if_neg (show ¬ f ((lo + hi) / 2) < k from hlt),
        if_neg (show ¬ k < f ((lo + hi) / 2) from hgt)]
      rfl
  | case4 lo hi h =>
      intro j hj1 hj2 hj3
      omega

/-- Binary search for the key `k` in the array `a`. -/
