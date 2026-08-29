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

open scoped BigOperators Real Classical NNReal

set_option maxHeartbeats 1000000

namespace KPZ

/-- Spatial derivative of a space-time function `h : time → space → ℝ`. -/

noncomputable def spaceDeriv (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => deriv (fun y => h t y) x

/-- `IsSolution xi h` says that `h : time → space → ℝ` is a classical solution of the
Kardar–Parisi–Zhang equation
`∂ₜ h = ∂ₓ² h + (∂ₓ h)² + ξ`
with forcing `xi`. -/
