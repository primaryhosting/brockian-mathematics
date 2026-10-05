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

theorem area_law_1d (d : ℕ) (C : ℝ) :
    ∃ K : ℝ, ∀ (n m : ℕ) (psi : Matrix (Fin m → Fin d) (Fin (n - m) → Fin d) ℂ),
      (psi * psiᴴ).trace = 1 →
      (∀ k : ℕ, ∃ s : Finset (Fin m → Fin d), s.card ≤ k ∧
          ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C / ((k : ℝ) + 1)) →
      entanglementEntropy psi ≤ K := by
  refine ⟨Real.log 2 + 2 * C, ?_⟩
  intro n m psi hnorm hdecay
  exact entropy_le_of_schmidt_truncation psi hnorm hdecay

/-- Variant of the area law under the stronger hypothesis of geometrically decaying Schmidt
truncation error. -/
