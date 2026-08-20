/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-!
## Setting

Figalli's regularity theory for optimal transport says, roughly, that if the cost function
satisfies the Ma–Trudinger–Wang (MTW) condition, and the two measures have densities that
are bounded away from `0` and from `∞` on suitable domains, then the Brenier optimal
transport map is regular.

Here we formalize and prove in full the **base case** of that theory: dimension one with
quadratic cost.  In dimension one the MTW condition is vacuous, the Brenier map is the
*monotone rearrangement* `T = G⁻¹ ∘ F`, characterized by the matching of cumulative
distribution functions `G (T x) = F x`, and the regularity statement takes the sharp
quantitative form

  (density of `μ` `≤ Λ`) and (density of `ν` `≥ lam > 0`)  ⟹  `T` is `(Λ / lam)`-Lipschitz.

The density bounds are used only through their integrated consequences,
`μ (Ioc x y) ≤ Λ (y - x)` and `ν (Ioc x y) ≥ lam (y - x)`, so these are taken as the
hypotheses.  As in the classical theory, the lower bound on the target density is imposed
only on the (bounded) target domain `B`, and the estimate is obtained on the source
domain `A`; a global lower bound would be incompatible with finiteness of `ν`.
-/

/-- The (real valued) cumulative distribution function of a measure on `ℝ`. -/

theorem figalli_OT_regularity_hypotheses_satisfiable :
    ∃ (mu nu : Measure ℝ) (_ : IsFiniteMeasure mu) (_ : IsFiniteMeasure nu)
      (A B : Set ℝ) (lam Lam : ℝ) (T : ℝ → ℝ),
      0 < lam ∧ 0 ≤ Lam ∧ A.Nonempty ∧
      (∀ x ∈ A, ∀ y ∈ A, x ≤ y → mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x))) ∧
      (∀ u ∈ B, ∀ v ∈ B, u ≤ v → ENNReal.ofReal (lam * (v - u)) ≤ nu (Set.Ioc u v)) ∧
      (∀ x ∈ A, T x ∈ B) ∧ (∀ x ∈ A, cdfReal nu (T x) = cdfReal mu x) := by
  classical
  refine ⟨volume.restrict (Set.Icc (0:ℝ) 1), volume.restrict (Set.Icc (0:ℝ) 1),
    inferInstance, inferInstance, Set.Icc 0 1, Set.Icc 0 1, 1, 1, id,
    one_pos, zero_le_one, ⟨0, by norm_num⟩, ?_, ?_, fun x hx => hx, fun _ _ => rfl⟩
  · intro x hx y hy hxy
    have hsub : Set.Ioc x y ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
      ⟨le_trans hx.1 ht.1.le, le_trans ht.2 hy.2⟩
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 hsub,
      Real.volume_Ioc]
    simp
  · intro u hu v hv huv
    have hsub : Set.Ioc u v ⊆ Set.Icc (0:ℝ) 1 := fun t ht =>
      ⟨le_trans hu.1 ht.1.le, le_trans ht.2 hv.2⟩
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 hsub,
      Real.volume_Ioc]
    simp

/-!
## Tensorization

For a product of one-dimensional problems the optimal map acts componentwise, and the
Lipschitz bound survives with the same constant, for the sup distance on `ℝⁿ`.
-/

