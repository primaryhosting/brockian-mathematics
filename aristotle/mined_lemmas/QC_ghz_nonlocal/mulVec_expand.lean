import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Matrix

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

namespace QC

/-- Index type for the computational basis of three qubits. -/
abbrev Idx : Type := Fin 2 × Fin 2 × Fin 2

/-- The (unnormalised) 3-qubit GHZ state `|000⟩ + |111⟩`. -/

private lemma mulVec_expand (M : Matrix Idx Idx ℂ) (i : Idx) :
    (M *ᵥ ghz) i = M i (0, 0, 0) + M i (1, 1, 1) := by
  simp only [Matrix.mulVec, dotProduct, ghz]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Prod.ext_iff, Fintype.sum_prod_type]

/-- Quantum prediction: `X ⊗ Y ⊗ Y` has the GHZ state as eigenvector with eigenvalue `-1`. -/
