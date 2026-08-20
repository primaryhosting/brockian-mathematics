import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem uu_mul_vv {ζ : F} (hζ : ζ ≠ 0) (i : Fin n) : uu ζ i * vv ζ i = 1 := by
  funext x
  cases h : x i
  · simp [uu, vv, h, bitv]
  · simp [uu, vv, h, bitv]; field_simp

/-- Splitting off the full product: `∏_{i∈S} u i = (∏_i u i) * ∏_{i ∉ S} v i`. -/
