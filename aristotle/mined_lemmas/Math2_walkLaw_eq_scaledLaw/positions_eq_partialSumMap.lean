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

theorem positions_eq_partialSumMap {a : ℕ → ℕ} (ha : Monotone a) (ha0 : a 0 = 0) (n k : ℕ)
    (ω : Ω) :
    (fun j : Fin k => (∑ i ∈ Finset.range (a ((j : ℕ) + 1)), X i ω) / Real.sqrt n)
      = partialSumMap k (fun j : Fin k =>
          (∑ i ∈ Finset.Ico (a j) (a (j + 1)), X i ω) / Real.sqrt n) := by
  funext j
  rw [partialSumMap]
  have := sum_Iic_fin k j
    (fun l => (∑ i ∈ Finset.Ico (a l) (a (l + 1)), X i ω) / Real.sqrt n)
  rw [this, ← Finset.sum_div,
    sum_blocks_eq_sum_range ha ha0 (fun i => X i ω) ((j : ℕ) + 1)]


/-- Weak convergence of the joint law of the rescaled increments to the product of the Gaussian
increment laws. -/
