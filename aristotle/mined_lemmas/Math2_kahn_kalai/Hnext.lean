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

noncomputable def Hnext (H : Finset (Finset α)) (W : Finset α) (m : ℕ) : Finset (Finset α) :=
  (H.filter (fun S => ¬ (m ≤ 2 * (minFrag H W S).card))).image (minFrag H W)

