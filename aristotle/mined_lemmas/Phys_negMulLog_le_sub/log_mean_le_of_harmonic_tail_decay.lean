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

theorem log_mean_le_of_harmonic_tail_decay {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) {C : ℝ}
    (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ C / ((k : ℝ) + 1)) :
    ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1) ≤ C := by
  calc ∑ i : Fin N, p i * Real.log (((i : ℕ) : ℝ) + 1)
      ≤ ∑ i : Fin N, (∑ k ∈ Finset.Ico 1 ((i : ℕ) + 1), (1 / (k : ℝ))) * p i := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (log_le_harmonic (i : ℕ)) (hp i)
    _ = ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ))
          * ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i :=
        weighted_layer_cake p (fun k => 1 / (k : ℝ))
    _ ≤ ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (C / ((k : ℝ) + 1)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (htail k) hk
    _ = C * ∑ k ∈ Finset.Ico 1 N, (1 / (k : ℝ)) * (1 / ((k : ℝ) + 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ C := by nlinarith [harmonic_tail_sum_le N]

/-- **Entropy estimate for inverse-linearly decaying tails.**  If the index-`k` tail mass of a
probability vector is at most `C/(k+1)`, its Shannon entropy is at most `log 2 + 2 C`, a bound
independent of the dimension `N`.  (This hypothesis is much weaker than geometric decay.) -/
