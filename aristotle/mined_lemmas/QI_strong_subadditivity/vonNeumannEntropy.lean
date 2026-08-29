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

noncomputable def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The reduced density matrix on the subsystem `A ⊗ B`, obtained by tracing out `C`. -/
