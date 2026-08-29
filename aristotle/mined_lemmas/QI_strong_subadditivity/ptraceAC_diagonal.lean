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

theorem ptraceAC_diagonal (p : A × B × C → ℝ) :
    ptraceAC (diagonal fun x => ((p x : ℝ) : ℂ)) = diagonal fun b => ((margB p b : ℝ) : ℂ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [ptraceAC, margB, diagonal_apply_eq, Complex.ofReal_sum]
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun a _ => ?_
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [diagonal_apply_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro _ h2 _
    exact absurd h2 h

variable (p : A × B × C → ℝ)

/-! ## Strong subadditivity of the von Neumann entropy -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai), for tripartite states
that are diagonal in a product basis.

If `ρ` is a density matrix on `A ⊗ B ⊗ C` which is diagonal in the product basis, with
diagonal given by a probability distribution `p`, then
`S(ABC) + S(B) ≤ S(AB) + S(BC)`,
where the subsystem states are the partial traces of `ρ`.

Note: only the case of states diagonal in a product basis is established here; the
general (noncommutative) Lieb–Ruskai inequality is not proved in this file. -/
