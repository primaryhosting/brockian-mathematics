import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace QPhys

open SchwartzMap

/-- The multiplication-by-`x` function `ℝ → ℂ` has temperate growth. -/

theorem hasTemperateGrowth_ofReal :
    Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) := by
  fun_prop

/-- The position operator `X : ψ ↦ (x ↦ x · ψ x)` on Schwartz space `𝓢(ℝ, ℂ)`. -/
