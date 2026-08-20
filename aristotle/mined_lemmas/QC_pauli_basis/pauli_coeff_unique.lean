import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

theorem pauli_coeff_unique {a b : Fin 4 → ℂ}
    (h : ∑ i, a i • pauli i = ∑ i, b i • pauli i) : a = b := by
  have hli := Fintype.linearIndependent_iff.mp pauli_linearIndependent
  funext i
  have h0 : ∑ i, (a i - b i) • pauli i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (hli (fun i => a i - b i) h0 i)

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

