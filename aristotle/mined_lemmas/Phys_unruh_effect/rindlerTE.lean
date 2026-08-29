/-
/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Real

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The Unruh temperature -/

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`. -/

noncomputable def rindlerTE (a c τ : ℝ) : ℝ := (c / a) * Real.sin (a * τ / c)

/-! ### Kinematics -/

