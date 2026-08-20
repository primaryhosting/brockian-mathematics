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

set_option grind.warning false

namespace QC

open Complex

/-- A pure state of a single qubit: a unit vector in `ℂ²`. -/
abbrev PureQubit : Type := Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1

/-- The 2-sphere `S²`, the unit sphere of `ℝ³`. -/
abbrev S2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1


lemma S2_ext (u p : EuclideanSpace ℝ (Fin 3)) (h0 : u 0 = p 0) (h1 : u 1 = p 1)
    (h2 : u 2 = p 2) : u = p := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i
  exacts [h0, h1, h2]

