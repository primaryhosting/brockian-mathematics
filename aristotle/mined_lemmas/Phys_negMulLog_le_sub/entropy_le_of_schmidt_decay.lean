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

theorem entropy_le_of_schmidt_decay (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1)
    {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hdecay : ∀ k : ℕ, ∃ s : Finset A, s.card ≤ k ∧
      ∑ i ∈ sᶜ, schmidtSpectrum psi i ≤ C * q ^ k) :
    entanglementEntropy psi ≤ (C * q / (1 - q)) * Real.log (1 / q) + Real.log (1 / (1 - q)) := by
  classical
  have hnn := schmidtSpectrum_nonneg psi
  have hs1 := sum_schmidtSpectrum psi hnorm
  have hC : 0 ≤ C := by
    obtain ⟨s, hs, hsum⟩ := hdecay 0
    have hse : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    rw [hse] at hsum
    simp only [Finset.compl_empty, pow_zero, mul_one] at hsum
    rw [hs1] at hsum
    linarith
  obtain ⟨e, htail⟩ := exists_sorted_tails (schmidtSpectrum psi) hnn hs1 (fun k => C * q ^ k) hdecay
  rw [entanglementEntropy_eq_reindex psi e]
  refine entropy_le_of_tail_decay (fun i => schmidtSpectrum psi (e i)) (fun i => hnn _) ?_
    hq0 hq1 hC htail
  rw [← hs1]
  exact Equiv.sum_comp e (schmidtSpectrum psi)

/-- **Entropy bound from inverse-linear Schmidt truncation error.**  If for every `k` the state
can be truncated to `k` Schmidt vectors with discarded weight at most `C/(k+1)`, then its
entanglement entropy is at most `log 2 + 2 C`: a constant depending only on `C`, independent of
the dimensions of the two factors. -/
