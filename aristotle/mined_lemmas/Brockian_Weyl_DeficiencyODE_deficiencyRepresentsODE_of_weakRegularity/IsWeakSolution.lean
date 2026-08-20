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
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- A *weak* (Carathéodory / integrated form) solution of the Sturm–Liouville equation
`u'' = (q - z) u` on the whole line: there is a continuous "quasi-derivative" `v` such that
`u` is the primitive of `v` and `v` is the primitive of `(q - z) u`.

This is the regularity that is available a priori for elements of the deficiency space of the
minimal operator `L u = -u'' + q u`: such an element is only known to solve the equation in the
integrated (distributional) sense. -/

def IsWeakSolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ v : ℝ → ℂ, Continuous v ∧
    (∀ x, u x = u 0 + ∫ t in (0:ℝ)..x, v t) ∧
    (∀ x, v x = v 0 + ∫ t in (0:ℝ)..x, (q t - z) * u t)

/-- A *classical* (pointwise, twice differentiable) solution of `u'' = (q - z) u`. -/
