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

theorem mean_le_of_tail_decay {N : ℕ} (p : Fin N → ℝ) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 ≤ C)
    (htail : ∀ k : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i ≤ C * q ^ k) :
    ∑ i : Fin N, (i : ℝ) * p i ≤ C * q / (1 - q) := by
  rw [mean_eq_sum_tails]
  calc ∑ k ∈ Finset.Ico 1 N, ∑ i ∈ Finset.univ.filter (fun i : Fin N => k ≤ (i : ℕ)), p i
      ≤ ∑ k ∈ Finset.Ico 1 N, C * q ^ k := Finset.sum_le_sum (fun k _ => htail k)
    _ ≤ C * q / (1 - q) := by
        have hrw : ∑ k ∈ Finset.Ico 1 N, C * q ^ k
            = ∑ k ∈ Finset.range (N - 1), (C * q) * q ^ k := by
          rw [Finset.sum_Ico_eq_sum_range]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [hrw]
        have hs : Summable (fun k : ℕ => (C * q) * q ^ k) :=
          (summable_geometric_of_lt_one hq0.le hq1).mul_left (C * q)
        refine (hs.sum_le_tsum _ (fun k _ => by positivity)).trans ?_
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
        ring_nf
        rfl

/-- **Entropy estimate for geometrically decaying tails.**  A probability vector whose
index-`k` tail mass is at most `C q ^ k` has Shannon entropy at most
`C q / (1 - q) * log (1/q) + log (1/(1-q))`: a bound depending only on `C` and `q`, in
particular independent of the dimension `N`. -/
