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

lemma wtOn_nonneg {s : Finset α} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset α) :
    0 ≤ wtOn s p A :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

