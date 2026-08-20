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

lemma wtOn_insert_mem {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ) {A : Finset α}
    (hA : A ⊆ s) : wtOn (insert x s) p (insert x A) = p * wtOn s p A := by
  have hxA : x ∉ A := fun h => hx (hA h)
  have h1 : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
  have h3 : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hxA
  have h2 : A.card ≤ s.card := Finset.card_le_card hA
  simp only [wtOn, h1, h3]
  rw [show s.card + 1 - (A.card + 1) = s.card - A.card by omega, pow_succ]
  ring

/-- Splitting a weighted sum over the powerset of `insert x s`. -/
