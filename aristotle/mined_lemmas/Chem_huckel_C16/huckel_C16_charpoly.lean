import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- A primitive 16-th root of unity. -/

theorem huckel_C16_charpoly :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly
      = ∏ k : Fin 16, (Polynomial.X
          - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 16) : ℝ) : ℂ)) := by
  obtain ⟨u, hconj⟩ := exists_unit_conj_diagonal
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

end Chem

