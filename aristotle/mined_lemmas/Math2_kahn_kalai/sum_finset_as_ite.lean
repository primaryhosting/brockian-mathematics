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

lemma sum_finset_as_ite (s : Finset (Finset α)) (f : Finset α → ℝ) :
    ∑ U ∈ s, f U = ∑ U : Finset α, if U ∈ s then f U else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext U; simp

/-- **Key Lemma.** If `H` is `m`-bounded with `m ≥ 1` and `r = c^2 * p`, then the expected
cost of the fragment cover `Ufam H W m` is at most `(2/c)^m`. -/
