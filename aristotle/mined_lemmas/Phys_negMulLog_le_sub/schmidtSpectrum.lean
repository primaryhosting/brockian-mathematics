import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

noncomputable def schmidtSpectrum (psi : Matrix A B ℂ) : A → ℝ :=
  (Matrix.isHermitian_mul_conjTranspose_self psi).eigenvalues

/-- The **entanglement entropy** of a bipartite pure state: the von Neumann entropy
`-∑ λ log λ` of its reduced density matrix. -/
