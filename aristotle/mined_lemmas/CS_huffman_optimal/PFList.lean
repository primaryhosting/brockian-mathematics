import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma PFList.eq_singleton_nil {L : List (List Bool)} (h : PFList L) (hm : [] ∈ L) :
    L = [[]] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
  have hp := List.pairwise_append.mp h
  obtain ⟨-, hp2, hcross⟩ := hp
  have hs : s = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact (hcross a ha [] (by simp)).2 (List.nil_prefix)
  have ht : t = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact (List.pairwise_cons.mp hp2).1 a ha |>.1 (List.nil_prefix)
  subst hs; subst ht; rfl

