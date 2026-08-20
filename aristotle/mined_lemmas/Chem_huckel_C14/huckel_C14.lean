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

theorem huckel_C14 :
    spectrum ℂ (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)) =
      {z : ℂ | ∃ k : Fin 14, z = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)} := by
  obtain ⟨u, hA⟩ := exists_unit_conj_diagonal
  rw [hA, spectrum.units_conjugate, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq, eigval, eq_comm]

/-- The characteristic polynomial of the adjacency matrix of `C₁₄` splits as
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`; this records the eigenvalues with multiplicity. -/
