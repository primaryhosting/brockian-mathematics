/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- Computational basis states of 4 qubits, indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 := Fin 4 → Fin 2

/-- The all-zeros bit string `|0000⟩`. -/

theorem ghz4_eq_superposition :
    ghz4 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZero (1 : ℂ) + EuclideanSpace.single allOne (1 : ℂ)) := by
  ext i
  by_cases h0 : i = allZero
  · subst h0
    simp [ghz4, EuclideanSpace.single_apply, allZero_ne_allOne]
  · by_cases h1 : i = allOne
    · subst h1
      simp [ghz4, EuclideanSpace.single_apply, h0]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

end QC

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

