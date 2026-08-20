/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Space-time functions and partial derivatives

A space-time function is modelled as `u : ℝ → ℝ → ℝ`, where `u t x` is its value at time `t`
and space point `x`. -/

/-- Time derivative of a space-time function. -/

def IsSHESolution (xi Z : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x, dt Z t x = dx (dx Z) t x + Z t x * xi t x

/-- Regularity class used throughout: differentiability in time, in space, and differentiability
in space of the first space derivative. -/
structure Regular (u : ℝ → ℝ → ℝ) : Prop where
  time : ∀ t x, DifferentiableAt ℝ (fun s => u s x) t
  space : ∀ t x, DifferentiableAt ℝ (fun y => u t y) x
  space2 : ∀ t x, DifferentiableAt ℝ (fun y => dx u t y) x

/-! ## The Cole–Hopf transform -/

section ColeHopf

variable {Z u : ℝ → ℝ → ℝ}

/-- Time derivative of the Cole–Hopf transform `log Z`. -/
