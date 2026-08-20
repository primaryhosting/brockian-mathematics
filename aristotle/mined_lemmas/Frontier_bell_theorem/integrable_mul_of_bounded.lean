/-!
# Bell Theorem
Category: Frontier Physics
Target: Frontier.bell_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

namespace Frontier

/-- Pointwise CHSH bound: for outcomes in `[-1, 1]` (deterministic hidden-variable outcomes),
the CHSH combination is bounded by `2`. -/

theorem integrable_mul_of_bounded {μ : Measure Λ} [IsProbabilityMeasure μ] {f g : Λ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, |f x| ≤ 1) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable (fun x => f x * g x) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  calc ‖f x * g x‖ = |f x| * |g x| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ 1 * 1 := by
        gcongr <;> [exact abs_nonneg _; exact hf1 x; exact hg1 x]
    _ = 1 := one_mul _
  
/-- **Bell's theorem / CHSH inequality for local hidden-variable models.**

A local hidden-variable model consists of a probability space `(Λ, μ)` of hidden variables
together with response functions `A₀, A₁` (Alice's two measurement settings) and `B₀, B₁`
(Bob's two settings), each taking values in `[-1, 1]`; the correlation predicted for a pair
of settings is `E(Aᵢ, Bⱼ) = ∫ Aᵢ Bⱼ dμ`.

The conclusion has two parts:

1. *(CHSH ≤ 2 classically.)* Every such model satisfies
   `E(A₀,B₀) + E(A₀,B₁) + E(A₁,B₀) - E(A₁,B₁) ≤ 2`.

2. *(No local hidden-variable model reproduces quantum mechanics.)* Consequently no such model
   can reproduce the quantum correlations of the singlet state at the optimal CHSH angles,
   namely `E(A₀,B₀) = E(A₀,B₁) = E(A₁,B₀) = √2/2` and `E(A₁,B₁) = -√2/2`, since those values
   give the CHSH combination the value `2√2 > 2`.
-/
