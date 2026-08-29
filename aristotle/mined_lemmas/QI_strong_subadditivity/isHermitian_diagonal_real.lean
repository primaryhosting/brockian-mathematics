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

theorem isHermitian_diagonal_real {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : ℂ)).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Pi.star_apply])

/-- The eigenvalues of a real diagonal matrix are its diagonal entries (as a multiset). -/
