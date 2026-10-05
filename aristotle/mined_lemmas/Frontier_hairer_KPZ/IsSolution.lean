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

def IsSolution (xi h : ℝ → ℝ → ℝ) : Prop :=
  ∀ t x : ℝ, HasDerivAt (fun s => h s x)
    (spaceDeriv (spaceDeriv h) t x + (spaceDeriv h t x) ^ 2 + xi t x) t

/-! ## Base case 1: the Cole–Hopf linearisation

If `w > 0` solves the heat equation `∂ₜ w = ∂ₓ² w`, then `h = log w` solves the
(unforced) KPZ equation. This is the classical transformation underlying the
solution theory of KPZ. -/

