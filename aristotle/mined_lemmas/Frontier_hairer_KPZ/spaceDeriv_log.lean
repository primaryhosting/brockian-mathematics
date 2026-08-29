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

theorem spaceDeriv_log (w wx : ℝ → ℝ → ℝ) (hpos : ∀ t x, 0 < w t x)
    (hx : ∀ t x, HasDerivAt (fun y => w t y) (wx t x) x) (t : ℝ) :
    spaceDeriv (fun t x => Real.log (w t x)) t = fun x => wx t x / w t x := by
  funext x
  exact ((hx t x).log (hpos t x).ne').deriv

