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


theorem continuousOn_classical_path {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousOn (fun s : ℝ => (1 - s) * (p - q) ^ 2 / (q + s * (p - q))) (uIcc (0:ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs
  exact ne_of_gt (pos_path hp hq hs)

/-- The classical (scalar) path identity underlying the integral representation of the
Kullback-Leibler divergence. -/
