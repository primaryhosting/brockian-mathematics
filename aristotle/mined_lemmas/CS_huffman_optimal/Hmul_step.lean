import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma Hmul_step (a b : ℝ) (t : Multiset ℝ) (hab : a ≤ b) (hbt : ∀ x ∈ t, b ≤ x) :
    Hmul (a ::ₘ b ::ₘ t) = (a + b) + Hmul ((a + b) ::ₘ t) := by
  have hts : (t.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have htmem : ∀ x ∈ t.sort (· ≤ ·), b ≤ x := by
    intro x hx
    exact hbt x (by rw [← Multiset.sort_eq t (· ≤ ·)]; exact hx)
  have hsorted : (a :: b :: t.sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨htmem, hts⟩⟩
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact h ▸ hab
    · exact hab.trans (htmem y h)
  have hs1 : (a ::ₘ b ::ₘ t).sort (· ≤ ·) = a :: b :: t.sort (· ≤ ·) := by
    have : ((a :: b :: t.sort (· ≤ ·) : List ℝ) : Multiset ℝ) = a ::ₘ b ::ₘ t := by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.sort_eq]
    rw [← this, sort_coe_of_sorted hsorted]
  have hins : ((a + b) ::ₘ t).sort (· ≤ ·)
      = List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) := by
    have hp : ((List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) : List ℝ) : Multiset ℝ)
        = (a + b) ::ₘ t := by
      have := List.perm_orderedInsert (α := ℝ) (· ≤ ·) (a + b) (t.sort (· ≤ ·))
      have h2 : ((List.orderedInsert (· ≤ ·) (a + b) (t.sort (· ≤ ·)) : List ℝ) : Multiset ℝ)
          = ((a + b) :: t.sort (· ≤ ·) : List ℝ) := Quot.sound this
      rw [h2, ← Multiset.cons_coe, Multiset.sort_eq]
    rw [← hp, sort_coe_of_sorted (List.Pairwise.orderedInsert _ _ hts)]
  rw [Hmul, Hmul, hs1, hins, hcost_cons_cons]


/-- A nonempty multiset in a linear order has a least element. -/
