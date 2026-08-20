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


theorem integrableOn_path (hρ : ρ.PosDef) (hσ : σ.PosDef) (htr : ρ.trace = σ.trace) :
    IntegrableOn (fun s : ℝ => (1 - s) * bkm (pathState ρ σ s) (ρ - σ)) (Ioo 0 1) := by
  have h := (integrable_uncurry_path hρ hσ).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact integral_res_quad_path hρ hσ htr (le_of_lt hs.1) (le_of_lt hs.2)

end QI

import RequestProject.QI.Spectral

/-!
# Resolvents and traces in an eigenbasis
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω : Mat n}

/-- The resolvent `(ω + t)⁻¹` of a matrix. -/
