/-
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The Pauli matrix `σ₁ = X`. -/

theorem span_pauli_eq_top :
    Submodule.span ℂ (Set.range pauli) = ⊤ := by
  obtain ⟨b, hb⟩ := pauli_basis
  rw [← hb, ← Module.Basis.span_eq b]

end QC

