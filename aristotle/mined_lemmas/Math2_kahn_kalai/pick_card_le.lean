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

lemma pick_card_le {H : Finset (Finset α)} {m : ℕ} (hH : ∀ S ∈ H, S.card ≤ m) (Z : Finset α) :
    (pick H Z).card ≤ m := by
  by_cases h : (H.filter (fun S => S ⊆ Z)).Nonempty
  · exact hH _ (pick_mem h).1
  · rw [pick, dif_neg h]
    simp

/-- The crucial observation: a large minimum fragment is contained in the canonical edge
of `W ∪ T`. -/
