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

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/

theorem huckel_C14_cycleGraph :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 14, (X - C ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)) := by
  rw [← adjC14_eq_adjMatrix_cycleGraph]
  exact huckel_C14

end

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

