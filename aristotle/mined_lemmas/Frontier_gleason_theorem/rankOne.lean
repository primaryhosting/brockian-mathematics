import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

def rankOne (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := Matrix.vecMulVec v (star v)

/-- A *quantum measure* (Gleason measure) on the projection lattice of `ℂ^N`:
a nonnegative, normalized, finitely additive function on orthogonal projections. -/
structure IsQuantumMeasure (μ : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop where
  nonneg : ∀ P, IsProj P → 0 ≤ μ P
  normalized : μ 1 = 1
  additive : ∀ P Q, IsProj P → IsProj Q → P * Q = 0 → μ (P + Q) = μ P + μ Q

/-- A density operator: a positive semidefinite matrix of unit trace. -/
