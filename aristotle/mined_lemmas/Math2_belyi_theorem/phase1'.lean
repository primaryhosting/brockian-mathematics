import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma phase1' (S : Finset ℂ) (hint : ∀ β ∈ S, IsIntegral ℚ β) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) :=
  phase1 (S.sup deg) S.card S hint (fun _ hβ => Finset.le_sup hβ) (Finset.card_filter_le _ _)

/-! ### The Belyi polynomial `x ↦ c · xᵐ (1-x)ⁿ` -/

/-- The normalising constant `(m+n)^(m+n) / (mᵐ nⁿ)` for `m = a+1`, `n = b+1`. -/
