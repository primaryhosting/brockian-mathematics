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

noncomputable def ptrA (ρ : Matrix (A × B × C) (A × B × C) ℂ) : Matrix (B × C) (B × C) ℂ :=
  fun x y => ∑ a, ρ (a, x.1, x.2) (a, y.1, y.2)

/-- The reduced density matrix on the subsystem `B`, obtained by tracing out `A` and `C`. -/
