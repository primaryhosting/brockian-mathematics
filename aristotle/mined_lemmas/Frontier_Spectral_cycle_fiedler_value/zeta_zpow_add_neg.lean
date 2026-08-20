/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

set_option grind.warning false

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma zeta_zpow_add_neg {n : ℕ} (m : ℤ) :
    zeta n ^ m + zeta n ^ (-m) = 2 * (Real.cos (2 * Real.pi * m / n) : ℂ) := by
  have h : ∀ a : ℤ, zeta n ^ a = Complex.exp (((2 * Real.pi * a / n : ℝ) : ℂ) * Complex.I) := by
    intro a
    rw [zeta_zpow]
    congr 1
    push_cast
    ring
  rw [h m, h (-m), Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [show (2 * (Real.pi : ℂ) * (-(m : ℂ)) / n) = -(2 * (Real.pi : ℂ) * (m : ℂ) / n) by ring,
    Complex.cos_neg, Complex.sin_neg]
  ring

/-! ## Elementary facts about `Fin n` arithmetic -/

