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

theorem isSolution_of_const_space (H g : ℝ → ℝ) :
    IsSolution (fun t _ => g t) (fun t _ => H t) ↔ ∀ t, HasDerivAt H (g t) t := by
  have hs : spaceDeriv (fun t _ : ℝ => H t) = fun _ _ => (0 : ℝ) := by
    funext t x; simp [spaceDeriv]
  constructor
  · intro h t
    have := h t 0
    rw [hs] at this
    simpa [spaceDeriv] using this
  · intro h t x
    rw [hs]
    simpa [spaceDeriv] using h t

