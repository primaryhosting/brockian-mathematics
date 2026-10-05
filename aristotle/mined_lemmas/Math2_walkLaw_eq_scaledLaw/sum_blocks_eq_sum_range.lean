import RequestProject.CLT

/-!
# Convergence of the rescaled walk against smooth test functions

`Math2.walkLaw μ n t` is the law of `S_{⌊n t⌋} / √n`, where `S` is a random walk with step
distribution `μ`.  Here we prove that, for a centered step distribution with unit variance and
finite third absolute moment, the integrals of smooth test functions against `walkLaw μ n t`
converge to the corresponding integrals against the centered Gaussian law of variance `t`, which
is the law of Brownian motion at time `t`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The law of `S_p / √n`, the sum of `p` i.i.d. steps with law `μ`, rescaled by `1/√n`. -/

theorem sum_blocks_eq_sum_range {a : ℕ → ℕ} (ha : Monotone a) (ha0 : a 0 = 0) (g : ℕ → ℝ)
    (m : ℕ) : ∑ l ∈ Finset.range m, ∑ i ∈ Finset.Ico (a l) (a (l + 1)), g i
      = ∑ i ∈ Finset.range (a m), g i := by
  induction m with
  | zero => simp [ha0]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive g (Nat.zero_le _) (ha (Nat.le_succ m))

/-- Rewriting a sum over `Finset.Iic j` in `Fin k` as a sum over a range of naturals. -/
