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

lemma mu_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Finset α)) : 0 ≤ mu p F :=
  Finset.sum_nonneg fun A _ => wt_nonneg hp0 hp1 A

