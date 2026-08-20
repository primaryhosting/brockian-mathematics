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

lemma wtOn_insert_not_mem {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ) {A : Finset α}
    (hA : A ⊆ s) : wtOn (insert x s) p A = (1 - p) * wtOn s p A := by
  have h1 : (insert x s).card = s.card + 1 := Finset.card_insert_of_notMem hx
  have h2 : A.card ≤ s.card := Finset.card_le_card hA
  simp only [wtOn, h1]
  rw [show s.card + 1 - A.card = (s.card - A.card) + 1 by omega, pow_succ]
  ring

