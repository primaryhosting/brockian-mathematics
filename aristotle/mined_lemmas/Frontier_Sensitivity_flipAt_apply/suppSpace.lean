import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

noncomputable def suppSpace {n : ℕ} (H : Finset (Q n)) : Submodule ℝ (Q n → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ (fun v : {v : Q n // v ∉ H} => (v : Q n)))

