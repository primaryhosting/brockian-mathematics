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

theorem ptraceA_diagonal (p : A × B × C → ℝ) :
    ptraceA (diagonal fun x => ((p x : ℝ) : ℂ)) = diagonal fun y => ((margBC p y : ℝ) : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [ptraceA, margBC, diagonal_apply_eq, Complex.ofReal_sum]
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [diagonal_apply_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _ h2
    exact absurd h2 h

omit [Fintype B] in
