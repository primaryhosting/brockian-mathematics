import RequestProject.Brockian.Weyl.DeficiencyODE

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring before the import line,
so this header is rendered as an ordinary block comment with identical content.)
-/

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

namespace Brockian.Weyl.DeficiencyODE

/-- The formally symmetric first-order Weyl differential expression
`τ u = -i u' + q u` with (continuous, real-valued in the symmetric case) potential `q`.

A function `u` is a *classical* solution of the deficiency equation `τ u = z u`
at the spectral parameter `z` when it is differentiable and satisfies the equation pointwise. -/

def SolvesDeficiencyODE (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  Differentiable ℝ u ∧ ∀ x : ℝ, -Complex.I * deriv u x + q x * u x = z * u x

/-- A *weak* deficiency element at the spectral parameter `z`: `u` is merely continuous and
satisfies the integrated (Volterra) form of `τ u = z u`, i.e.
`u x = u 0 + ∫ t in 0..x, i (z - q t) u t`.

This is the form in which deficiency elements of the minimal operator are produced: a priori one
only knows that `u` is (locally integrable and) a distributional solution, with the integrated
identity coming from the definition of the adjoint, and *not* that `u` is differentiable. -/
