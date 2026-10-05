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

theorem entanglementEntropy_eq_reindex (psi : Matrix A B ℂ) (e : Fin (Fintype.card A) ≃ A) :
    entanglementEntropy psi = ∑ i, Real.negMulLog (schmidtSpectrum psi (e i)) :=
  (Equiv.sum_comp e (fun a => Real.negMulLog (schmidtSpectrum psi a))).symm

/-- If the state can be truncated to `k` Schmidt vectors with discarded weight at most `C q ^ k`,
its entanglement entropy is bounded by an explicit constant depending only on `C` and `q`. -/
