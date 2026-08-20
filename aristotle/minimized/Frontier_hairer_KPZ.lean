import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module documentation, so this header comment
appears immediately after the single `import Mathlib` line.)
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
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Partial derivatives on space-time `ℝ × ℝ`

A point `p : ℝ × ℝ` is read as `(t, x)` with `t` the time variable and `x` the space variable. -/

/-- Partial derivative in the time variable of a space-time function. -/

noncomputable def dt (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun s : ℝ => f (s, p.2)) p.1

/-- Partial derivative in the space variable of a space-time function. -/

noncomputable def dx (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun y : ℝ => f (p.1, y)) p.2

/-- `IsHeatSolution Z` says that `Z : ℝ × ℝ → ℝ` is a strictly positive classical solution of
the linear heat equation `∂_t Z = ∂_x² Z`, with enough regularity in the space variable for the
second space derivative to be taken at every point. -/
structure IsHeatSolution (Z : ℝ × ℝ → ℝ) : Prop where
  /-- `Z` is everywhere strictly positive. -/
  pos : ∀ p : ℝ × ℝ, 0 < Z p
  /-- `Z` is differentiable in space. -/
  diff_x : ∀ t : ℝ, Differentiable ℝ (fun y : ℝ => Z (t, y))
  /-- The space derivative of `Z` is again differentiable in space. -/
  diff_xx : ∀ t : ℝ, Differentiable ℝ (fun y : ℝ => dx Z (t, y))
  /-- `Z` is differentiable in time. -/
  diff_t : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun s : ℝ => Z (s, p.2)) p.1
  /-- The heat equation `∂_t Z = ∂_x² Z`. -/
  heat : ∀ p : ℝ × ℝ, dt Z p = dx (dx Z) p

/-- `IsKPZSolution h` says that `h : ℝ × ℝ → ℝ` solves the noiseless (deterministic) KPZ
equation `∂_t h = ∂_x² h + (∂_x h)²`. -/

def IsKPZSolution (h : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, dt h p = dx (dx h) p + (dx h p) ^ 2

/-! ## The Cole–Hopf reduction -/

/-- The space derivative of the Cole–Hopf transform `log Z`. -/
