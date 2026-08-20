import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma mem_suppSpace_iff {n : ℕ} (H : Finset (Q n)) (y : Q n → ℝ) :
    y ∈ suppSpace H ↔ ∀ v, v ∉ H → y v = 0 := by
  constructor
  · intro hy v hv
    exact congrFun hy ⟨v, hv⟩
  · intro hy
    funext v
    exact hy v.1 v.2

