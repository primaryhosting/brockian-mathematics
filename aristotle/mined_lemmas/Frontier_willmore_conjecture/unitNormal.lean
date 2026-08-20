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

noncomputable def unitNormal (R r u v : ℝ) : E3 :=
  ((nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).1,
   (nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).2.1,
   (nrm3 (normalVec R r u v))⁻¹ * (normalVec R r u v).2.2)

/-- Coefficient `E` of the first fundamental form. -/
