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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem trace_diag_mul_diag (A B : Mat n) (d e : Fin n → ℂ) :
    (A * Matrix.diagonal d * B * Matrix.diagonal e).trace = ∑ i, ∑ j, A i j * d j * B j i * e i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_mul, mul_ite,
    Finset.sum_ite_eq']

end QI

import RequestProject.QI.DPI

/-!
# The Holevo bound

The accessible information of an ensemble of quantum states is at most its Holevo `χ` quantity.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
  {p : X → ℝ} {ρ : X → Mat n} {E : Y → Mat n}

