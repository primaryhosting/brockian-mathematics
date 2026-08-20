/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Polynomial

/-- A primitive 17-th root of unity. -/

theorem huckel_C17_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 17).adjMatrix ℂ) =
      Set.range (fun k : Fin 17 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := F17_isUnit
  have hA : ((SimpleGraph.cycleGraph 17).adjMatrix ℂ) = u.val * D17 * u⁻¹.val := by
    rw [← A17, A17_eq_conj, Matrix.coe_units_inv, hu]
  rw [hA, spectrum.units_conjugate, D17, spectrum_diagonal]

end Chem

