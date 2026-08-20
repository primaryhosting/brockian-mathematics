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

namespace QC

open Matrix
open scoped Kronecker

/-- Index type for three qubits. -/
abbrev Idx : Type := (Fin 2 × Fin 2) × Fin 2

/-- A measurement setting for one party: `false` means measure the Pauli `X`
observable, `true` means measure the Pauli `Y` observable. -/
abbrev Setting : Type := Bool

/-- The Pauli `X` matrix. -/

theorem ghz_normalized : ∑ i : Idx, Complex.normSq (ghz i) = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [ghz, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  field_simp
  nlinarith [h2, Real.sqrt_nonneg 2]

