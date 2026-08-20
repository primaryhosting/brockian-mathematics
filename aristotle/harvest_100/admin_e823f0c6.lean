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
def bsearch (f : ℕ → α) (k : α) (lo hi : ℕ) : Option ℕ :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if f mid < k then bsearch f k (mid + 1) hi
    else if k < f mid then bsearch f k lo mid
    else some mid
  else none
termination_by hi - lo
decreasing_by
  · omega
  · omega

/-- Soundness: any index returned by `bsearch` lies in the searched range and
carries the key. No sortedness assumption is needed. -/
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
def binarySearch [Inhabited α] (a : Array α) (k : α) : Option ℕ :=
  bsearch (fun i => a[i]!) k 0 a.size

/-- **Binary search is correct.** On a sorted array `a`, the binary search for a key `k`
returns an index if and only if `k` occurs in `a`; moreover any index it returns is a
valid index of `a` holding the key `k`. -/
theorem binary_search_correct [Inhabited α] (a : Array α) (k : α)
    (hsorted : ∀ i j : ℕ, i ≤ j → j < a.size → a[i]! ≤ a[j]!) :
    (∀ i, binarySearch a k = some i → i < a.size ∧ a[i]! = k) ∧
      ((binarySearch a k).isSome ↔ ∃ i, i < a.size ∧ a[i]! = k) := by
  constructor
  · intro i hi
    have hres := bsearch_sound (fun i => a[i]!) k 0 a.size i hi
    exact ⟨hres.2.1, hres.2.2⟩
  · constructor
    · intro hsome
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
      have hres := bsearch_sound (fun i => a[i]!) k 0 a.size i hi
      exact ⟨i, hres.2.1, hres.2.2⟩
    · rintro ⟨i, hi1, hi2⟩
      exact bsearch_complete (fun i => a[i]!) k a.size hsorted 0 a.size le_rfl i
        (Nat.zero_le i) hi1 hi2

end CS

