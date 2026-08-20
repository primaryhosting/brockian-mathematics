import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

noncomputable def P12 : Matrix (Fin 12) (Fin 12) ℂ := Matrix.vandermonde (fun j => om ^ (j : ℕ))

/-- The diagonal matrix of eigenvalues. -/
