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

noncomputable def ptrAC (ρ : Matrix (A × B × C) (A × B × C) ℂ) : Matrix B B ℂ :=
  fun x y => ∑ a, ∑ c, ρ (a, x, c) (a, y, c)

/-! ## The entropy of a diagonal matrix -/

