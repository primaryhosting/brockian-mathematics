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

theorem IsC3Test.convPow_swap_bound (h : IsC3Test f f1 f2 f3 M) {P Q : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP1 : ∫ x, x ∂P = 0) (hQ1 : ∫ x, x ∂Q = 0)
    (hPQ2 : ∫ x, x ^ 2 ∂P = ∫ x, x ^ 2 ∂Q)
    (hP3 : Integrable (fun x : ℝ => |x| ^ 3) P) (hQ3 : Integrable (fun x : ℝ => |x| ^ 3) Q) :
    ∀ (m : ℕ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      |(∫ x, f x ∂(ρ ∗ convPow P m)) - ∫ x, f x ∂(ρ ∗ convPow Q m)|
        ≤ m * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q)) := by
  intro m
  induction m with
  | zero => intro ρ _; simp
  | succ m ih =>
      intro ρ _
      have hK : 0 ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
        have h1 : 0 ≤ ∫ x, |x| ^ 3 ∂P := integral_nonneg fun x => by positivity
        have h2 : 0 ≤ ∫ x, |x| ^ 3 ∂Q := integral_nonneg fun x => by positivity
        have := h.nonneg
        positivity
      have e1 : ρ ∗ convPow P (m + 1) = (ρ ∗ P) ∗ convPow P m := by
        rw [convPow_succ, ← Measure.conv_assoc, conv_swap_right]
      have e2 : (ρ ∗ P) ∗ convPow Q m = (ρ ∗ convPow Q m) ∗ P := conv_swap_right _ _ _
      have e3 : ρ ∗ convPow Q (m + 1) = (ρ ∗ convPow Q m) ∗ Q := by
        rw [convPow_succ, ← Measure.conv_assoc]
      have hstep : |(∫ x, f x ∂((ρ ∗ convPow Q m) ∗ P)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)|
          ≤ M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) :=
        h.conv_swap_bound hP1 hQ1 hPQ2 hP3 hQ3
      have hih := ih (ρ ∗ P)
      rw [e1, e3]
      calc |(∫ x, f x ∂((ρ ∗ P) ∗ convPow P m)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)|
          ≤ |(∫ x, f x ∂((ρ ∗ P) ∗ convPow P m)) - ∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)|
            + |(∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)) - ∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q)| := by
            simpa using abs_sub_le (∫ x, f x ∂((ρ ∗ P) ∗ convPow P m))
              (∫ x, f x ∂((ρ ∗ P) ∗ convPow Q m)) (∫ x, f x ∂((ρ ∗ convPow Q m) ∗ Q))
        _ ≤ m * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q))
              + M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q) := by
            refine add_le_add hih ?_
            rw [e2]
            exact hstep
        _ = (m + 1 : ℕ) * (M * ((∫ x, |x| ^ 3 ∂P) + ∫ x, |x| ^ 3 ∂Q)) := by push_cast; ring

end Math2

import RequestProject.ConvPow

/-!
# Random walks with i.i.d. steps

We show that the law of the partial sum `X 0 + ⋯ + X (m-1)` of an i.i.d. sequence with common
law `μ` is the `m`-fold convolution power `convPow μ m`.
-/

namespace Math2

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The law of the sum of the coordinates of a finite product measure is the convolution power. -/
