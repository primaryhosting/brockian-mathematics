/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

theorem huckel_C14_charpoly :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)).charpoly =
      ∏ k : Fin 14, (Polynomial.X -
        Polynomial.C ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)) := by
  obtain ⟨u, hA⟩ := exists_unit_conj_diagonal
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

end Chem

