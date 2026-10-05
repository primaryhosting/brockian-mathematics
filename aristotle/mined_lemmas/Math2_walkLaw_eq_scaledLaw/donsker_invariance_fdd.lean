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

theorem donsker_invariance_fdd (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, P.map (X i) = μ) (hmean : ∫ y, y ∂μ = 0) (hvar : ∫ y, y ^ 2 ∂μ = 1)
    (h3 : Integrable (fun y : ℝ => |y| ^ 3) μ) {t : ℕ → ℝ} (hmono : Monotone t) (ht0 : t 0 = 0)
    (k : ℕ) (f : (Fin k → ℝ) →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, f (fun j : Fin k =>
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) ∂P) atTop
      (𝓝 (∫ z, f z ∂(brownianFdd t k))) := by
  -- the times, as numbers of steps
  have ha : ∀ n : ℕ, Monotone (fun j : ℕ => ⌊(n : ℝ) * t j⌋₊) := by
    intro n i j hij
    refine Nat.floor_le_floor ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := hmono hij
    nlinarith
  have ha0 : ∀ n : ℕ, (fun j : ℕ => ⌊(n : ℝ) * t j⌋₊) 0 = 0 := by
    intro n
    simp [ht0]
  -- the law of the vector of rescaled positions
  have hmeasv : ∀ n : ℕ, Measurable (fun (ω : Ω) (j : Fin k) =>
      (∑ i ∈ Finset.Ico (⌊(n : ℝ) * t (j : ℕ)⌋₊) (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊), X i ω)
        / Real.sqrt n) := by
    intro n
    exact measurable_pi_lambda _ fun j => (measurable_blockSum hmeas _ _).div_const _
  have hlaw : ∀ n : ℕ, P.map (fun (ω : Ω) (j : Fin k) =>
        (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n)
      = (Measure.pi (fun j : Fin k =>
          scaledLaw μ (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊ - ⌊(n : ℝ) * t (j : ℕ)⌋₊) n)).map
            (partialSumMap k) := by
    intro n
    have hpos : (fun (ω : Ω) (j : Fin k) =>
          (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n)
        = (partialSumMap k) ∘ (fun (ω : Ω) (j : Fin k) =>
            (∑ i ∈ Finset.Ico (⌊(n : ℝ) * t (j : ℕ)⌋₊) (⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊), X i ω)
              / Real.sqrt n) := by
      funext ω
      exact positions_eq_partialSumMap (ha n) (ha0 n) n k ω
    rw [hpos, ← Measure.map_map (measurable_partialSumMap k) (hmeasv n),
      map_scaledIncrements hmeas hindep hident (ha n) n k]
  -- weak convergence of the increments, transported by the partial sum map
  have hconv := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_incrementsProb (μ := μ) hmean hvar h3 hmono ht0 k) (continuous_partialSumMap k)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv
  have hint := hconv f
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    scaledProb_toMeasure, brownianProb_toMeasure] at hint
  have hlimit : (Measure.pi (fun j : Fin k =>
      gaussianReal 0 (t ((j : ℕ) + 1) - t (j : ℕ)).toNNReal)).map (partialSumMap k)
      = brownianFdd t k := rfl
  rw [hlimit] at hint
  refine hint.congr fun n => ?_
  have hmeaspos : Measurable (fun (ω : Ω) (j : Fin k) =>
      (∑ i ∈ Finset.range ⌊(n : ℝ) * t ((j : ℕ) + 1)⌋₊, X i ω) / Real.sqrt n) :=
    measurable_pi_lambda _ fun j =>
      (Finset.measurable_sum _ fun i _ => hmeas i).div_const _
  rw [← hlaw n, integral_map hmeaspos.aemeasurable f.continuous.aestronglyMeasurable]

end Walk

end Fdd

end Math2

import Mathlib

/-!
# Third order Taylor bounds for test functions

This file introduces the class of test functions used in the Lindeberg swapping argument:
functions `f : ℝ → ℝ` which are bounded, three times differentiable with a bounded third
derivative.  For such a function we prove the crude Taylor estimate

`|f (w + u) - f w - f' w * u - f'' w * u ^ 2 / 2| ≤ M * |u| ^ 3`.
-/

namespace Math2

open Set

/-- `IsC3Test f f1 f2 f3 M` says that `f1, f2, f3` are the first three derivatives of `f`,
that `|f| ≤ M` and that `|f3| ≤ M`. -/
structure IsC3Test (f f1 f2 f3 : ℝ → ℝ) (M : ℝ) : Prop where
  hasDeriv0 : ∀ x, HasDerivAt f (f1 x) x
  hasDeriv1 : ∀ x, HasDerivAt f1 (f2 x) x
  hasDeriv2 : ∀ x, HasDerivAt f2 (f3 x) x
  bound0 : ∀ x, |f x| ≤ M
  bound3 : ∀ x, |f3 x| ≤ M

namespace IsC3Test

variable {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}

