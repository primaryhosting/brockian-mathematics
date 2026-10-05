/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma pd2_eq {f g : ℝ → ℝ → ℝ} (h : ∀ u v, HasDerivAt (fun t => f u t) (g u v) v) :
    pd2 f = g := by
  funext u v; exact (h u v).deriv

/-! ## Parametrized surfaces in `ℝ³` and their Willmore energy

A parametrized surface is given by its three real coordinate functions of two parameters
`(u, v)`.  All the classical local invariants (first and second fundamental forms, mean
curvature, area element) are defined by the standard formulas of classical surface theory. -/

/-- A parametrized surface in `ℝ³`, given by its three coordinate functions. -/
structure ParamSurface where
  /-- First coordinate function. -/
  x : ℝ → ℝ → ℝ
  /-- Second coordinate function. -/
  y : ℝ → ℝ → ℝ
  /-- Third coordinate function. -/
  z : ℝ → ℝ → ℝ

namespace ParamSurface

variable (S : ParamSurface)

/-- Coefficient `E = ⟨f_u, f_u⟩` of the first fundamental form. -/
