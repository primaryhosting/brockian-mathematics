/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem margB_nonneg (hp0 : ∀ x, 0 ≤ p x) (b : B) : 0 ≤ margB p b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hp0 _

/-! ## The classical (Shannon) strong subadditivity inequality -/

/-- Pointwise Gibbs-type inequality: `p - q ≤ p * log (p / q)`. -/
