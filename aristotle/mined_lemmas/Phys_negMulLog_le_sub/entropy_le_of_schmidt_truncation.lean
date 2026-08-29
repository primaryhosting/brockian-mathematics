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

theorem entropy_le_of_schmidt_truncation (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    {C : ℝ}
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C / ((k : ℝ) + 1)) :
    entanglementEntropy psi ≤ Real.log 2 + 2 * C := by
  classical
  have hnn := schmidtSpectrum_nonneg psi
  have hs1 := sum_schmidtSpectrum psi hnorm
  have hC : 0 ≤ C := by
    obtain ⟨s, hs, hsum⟩ := hdecay 0
    have hse : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    rw [hse] at hsum
    simp only [Finset.compl_empty, Nat.cast_zero, zero_add, div_one] at hsum
    rw [hs1] at hsum
    linarith
  obtain ⟨e, htail⟩ :=
    exists_sorted_tails (schmidtSpectrum psi) hnn hs1 (fun k => C / ((k : ℝ) + 1)) hdecay
  rw [entanglementEntropy_eq_reindex psi e]
  refine entropy_le_of_harmonic_tail_decay (fun i => schmidtSpectrum psi (e i)) (fun i => hnn _) ?_
    hC htail
  rw [← hs1]
  exact Equiv.sum_comp e (schmidtSpectrum psi)

/-- **Consistency of the truncation hypothesis.**  Every normalized bipartite pure state admits
a truncation bound with *some* constant; the content of the area law is that for gapped
one-dimensional chains the constant can be chosen independently of the system size.  In
particular the hypothesis of `Phys.area_law_1d` is satisfiable. -/
