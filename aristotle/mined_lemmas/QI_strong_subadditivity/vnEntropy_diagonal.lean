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

theorem vnEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (diagonal fun i => ((d i : ℝ) : ℂ)) = ∑ i, Real.negMulLog (d i) := by
  have h := isHermitian_diagonal_real d
  rw [vnEntropy, dif_pos h]
  have key := congrArg (fun m => (Multiset.map Real.negMulLog m).sum)
    (eigenvalues_diagonal_multiset d h)
  simpa [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using key

section Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-! ## Marginals of a joint distribution -/

/-- The `A × B` marginal of a distribution on `A × B × C`. -/
