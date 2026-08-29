import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Real
open scoped ComplexOrder

namespace QI

/-! ## Von Neumann entropy and reduced density matrices -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a matrix, computed as the sum of
`negMulLog` over the eigenvalues.  (Defined to be `0` on non-Hermitian matrices.) -/

theorem classical_ssa (p : A × B × C → ℝ) (hp : ∀ x, 0 ≤ p x) :
    (∑ x, Real.negMulLog (p x)) + ∑ b, Real.negMulLog (∑ a, ∑ c, p (a, b, c))
      ≤ (∑ a, ∑ b, Real.negMulLog (∑ c, p (a, b, c)))
        + ∑ b, ∑ c, Real.negMulLog (∑ a, p (a, b, c)) :=
  classical_ssa_aux p hp _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

/-! ## Strong subadditivity -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai), for a tripartite
density matrix `ρ` on `A ⊗ B ⊗ C` that is diagonal in the product basis:
`S(ABC) + S(B) ≤ S(AB) + S(BC)`.

The normalisation hypothesis `htr : ρ.trace = 1` is part of the definition of a density
matrix; the proof does not actually need it. -/
