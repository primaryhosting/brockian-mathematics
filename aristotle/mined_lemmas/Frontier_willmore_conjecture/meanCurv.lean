/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/

noncomputable def meanCurv (R r u v : ℝ) : ℝ :=
  (secondE R r u v * firstG R r u v - 2 * secondF R r u v * firstF R r u v
      + secondG R r u v * firstE R r u v)
    / (2 * (firstE R r u v * firstG R r u v - firstF R r u v ^ 2))

/-- The area element `√(EG - F²)`. -/
