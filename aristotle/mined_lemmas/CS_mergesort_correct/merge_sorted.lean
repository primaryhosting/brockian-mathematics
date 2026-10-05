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

theorem merge_sorted {le : α → α → Bool}
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b ∨ le b a) :
    ∀ xs ys : List α, List.Pairwise (fun a b => le a b = true) xs →
      List.Pairwise (fun a b => le a b = true) ys →
      List.Pairwise (fun a b => le a b = true) (merge le xs ys) := by
  intro xs ys
  induction xs, ys using merge.induct (le := le) with
  | case1 ys => simp
  | case2 xs h => simp
  | case3 x xs y ys h ih =>
      intro hx hy
      rw [merge_cons_cons, if_pos h]
      rw [List.pairwise_cons] at hx ⊢
      refine ⟨?_, ih hx.2 hy⟩
      intro z hz
      rcases mem_merge.1 hz with hz | hz
      · exact hx.1 z hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact htrans x y z h ((List.pairwise_cons.1 hy).1 z hz)
  | case4 x xs y ys h ih =>
      intro hx hy
      rw [merge_cons_cons, if_neg h]
      have hyx : le y x = true := by
        rcases htotal x y with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.pairwise_cons] at hy ⊢
      refine ⟨?_, ih hx hy.2⟩
      intro z hz
      rcases mem_merge.1 hz with hz | hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hyx
        · exact htrans y x z hyx ((List.pairwise_cons.1 hx).1 z hz)
      · exact hy.1 z hz

/-- Mergesort with respect to a boolean comparison `le`. -/
