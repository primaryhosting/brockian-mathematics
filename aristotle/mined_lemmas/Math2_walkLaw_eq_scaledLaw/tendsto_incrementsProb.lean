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

theorem tendsto_incrementsProb (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℕ → ℝ} (hmono : Monotone t) (ht0 : t 0 = 0)
    (k : ℕ) :
    Tendsto (fun n : ℕ => ProbabilityMeasure.pi (fun j : Fin k =>
        scaledProb μ (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊ - ⌊(n : ℝ) * t (j : ℕ)⌋₊) n)) atTop
      (𝓝 (ProbabilityMeasure.pi
        (fun j : Fin k => brownianProb (t ((j : ℕ) + 1) - t (j : ℕ))))) := by
  refine (ProbabilityMeasure.continuous_pi.tendsto _).comp (tendsto_pi_nhds.2 fun j => ?_)
  have hs : 0 ≤ t (j : ℕ) := by
    rw [← ht0]; exact hmono (Nat.zero_le _)
  have hsu : t (j : ℕ) ≤ t ((j : ℕ) + 1) := hmono (Nat.le_succ _)
  exact tendsto_scaledProb hmean hvar h3 (tendsto_floor_diff_div hs hsu)

/-- **Donsker's invariance principle: convergence of the finite dimensional distributions.**

Let `X 0, X 1, …` be i.i.d. real random variables with common law `μ`, centred, of unit variance
and with a finite third absolute moment, and let `S_m = X 0 + ⋯ + X (m-1)` be the associated
random walk.  Fix times `0 = t 0 ≤ t 1 ≤ ⋯`.  Then the random vector

`(S_{⌊n·t 1⌋}/√n, …, S_{⌊n·t k⌋}/√n)`

converges in distribution, as `n → ∞`, to `(B_{t 1}, …, B_{t k})`, the vector of the values of a
Brownian motion at the times `t 1, …, t k`, described here as the partial sums of independent
centred Gaussian increments of variances `t (j+1) - t j`. -/
