import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma hforest_isSome : ∀ (F : List (ℝ × HTree ι)), F ≠ [] → ∃ T, hforest F = some T := by
  intro F
  induction F using hforest.induct with
  | case1 => intro h; exact absurd rfl h
  | case2 a t => intro _; exact ⟨t, by rw [hforest]⟩
  | case3 a s b t rest ih =>
      intro _
      have hne : List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
          (a + b, HTree.node s t) rest ≠ [] := by
        intro h
        have := (List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
          (a + b, HTree.node s t) rest).length_eq
        rw [h] at this
        simp at this
      obtain ⟨T, hT⟩ := ih hne
      exact ⟨T, by rw [hforest]; exact hT⟩

omit [DecidableEq ι] in
