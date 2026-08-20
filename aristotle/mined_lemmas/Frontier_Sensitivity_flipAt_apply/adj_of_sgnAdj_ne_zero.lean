import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma adj_of_sgnAdj_ne_zero {n : ℕ} {u v : Q n} (h : sgnAdj v u ≠ 0) : adj u v := by
  by_contra hadj
  refine h (sgnAdj_eq_zero_of_forall ?_)
  intro k hk
  exact hadj (hk ▸ adj_flipAt v k)

/-! #### The key matrix identity `A² = n • 1` -/

