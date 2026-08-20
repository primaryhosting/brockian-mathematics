/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma minFrag_subset_pick {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ⊆ pick H (W ∪ minFrag H W S) := by
  set T := minFrag H W S with hT
  set Z := W ∪ T with hZ
  obtain ⟨S', hS'H, hS'sub, hEq⟩ := minFrag_eq (W := W) hS
  have hS'Z : S' ⊆ Z := by
    intro x hx
    rw [hZ, Finset.mem_union]
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (by rw [hT, hEq, Finset.mem_sdiff]; exact ⟨hx, hxW⟩)
  have hne : (H.filter (fun S => S ⊆ Z)).Nonempty := ⟨S', Finset.mem_filter.2 ⟨hS'H, hS'Z⟩⟩
  obtain ⟨hPH, hPZ⟩ := pick_mem hne
  -- `pick H Z` is a candidate fragment for `S`
  have hTS : T ⊆ S := minFrag_subset hS
  have hPWS : pick H Z ⊆ W ∪ S := by
    intro x hx
    rcases Finset.mem_union.1 (hPZ hx) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hTS h)
  have hmin : T.card ≤ (pick H Z \ W).card := minFrag_min hS hPH hPWS
  have hsub : pick H Z \ W ⊆ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.1 (hPZ hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have : pick H Z \ W = T := Finset.eq_of_subset_of_card_le hsub hmin
  rw [← this]
  exact Finset.sdiff_subset

end KahnKalai

/-
Basic set-up for the Kahn-Kalai theorem: the product measure `mu p` on the
powerset of a finite type, up-sets, covers and their costs.
-/
import RequestProject.Weights

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `wt p A` is the probability that the `p`-random subset of the ground type equals `A`. -/
