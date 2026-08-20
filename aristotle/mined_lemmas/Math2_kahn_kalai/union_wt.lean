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

lemma union_wt (a b : ℝ) (f : Finset α → ℝ) :
    ∑ A : Finset α, ∑ B : Finset α, wt a A * wt b B * f (A ∪ B)
      = ∑ C : Finset α, wt (a + b - a * b) C * f C := by
  have h : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    rw [Finset.powerset_univ]
  rw [h]
  exact union_wtOn a b _ f

/-- The measure of a family of sets. -/
