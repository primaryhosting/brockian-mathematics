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


theorem integrableOn_classical_path {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (Ioo 0 1) := by
  have h : IntegrableOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using continuousOn_classical_path hp hq
  exact h.mono_set Set.Ioo_subset_Icc_self

end QI

import RequestProject.QI.Measurement
import RequestProject.QI.PathIdentity

/-!
# Monotonicity of the relative entropy under measurements

The Umegaki relative entropy of two faithful states dominates the Kullback-Leibler divergence
of the outcome distributions of any POVM measurement performed on them.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ρ σ : Mat n} {Y : Type*} [Fintype Y] {E : Y → Mat n}

/-- **Data processing inequality for measurements.** -/
