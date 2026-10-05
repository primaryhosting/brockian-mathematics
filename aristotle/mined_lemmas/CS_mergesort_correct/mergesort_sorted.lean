/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u}

/-- Split a list into two lists by alternately distributing its elements. -/

theorem mergesort_sorted {le : α → α → Bool}
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b ∨ le b a) :
    ∀ l : List α, List.Pairwise (fun a b => le a b = true) (mergesort le l) := by
  intro l
  induction l using mergesort.induct with
  | case1 => simp [mergesort]
  | case2 a => simp [mergesort]
  | case3 a b l ih1 ih2 =>
      rw [mergesort_cons_cons]
      exact merge_sorted htrans htotal _ _ ih1 ih2

/-- **Mergesort is correct**: for a transitive and total boolean comparison `le`,
`mergesort le l` is sorted with respect to `le` and is a permutation of `l`. -/
