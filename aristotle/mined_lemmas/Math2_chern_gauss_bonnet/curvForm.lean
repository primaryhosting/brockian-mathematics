/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

noncomputable def curvForm {m : ℕ} (v : Fin (2 * m) → V) (i j : Fin (2 * m)) :
    ExteriorAlgebra ℝ V :=
  ExteriorAlgebra.ι ℝ (v i) * ExteriorAlgebra.ι ℝ (v j)

/-- The ordered product `Ω_{01} ∧ Ω_{23} ∧ ⋯ ∧ Ω_{(2m-2)(2m-1)}` of curvature two-forms. -/
