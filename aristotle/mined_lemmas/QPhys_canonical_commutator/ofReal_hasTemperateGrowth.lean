/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/

theorem ofReal_hasTemperateGrowth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth

/-- The position operator `X : f ↦ (x ↦ x * f x)` on the Schwartz space `𝓢(ℝ, ℂ)`. -/
