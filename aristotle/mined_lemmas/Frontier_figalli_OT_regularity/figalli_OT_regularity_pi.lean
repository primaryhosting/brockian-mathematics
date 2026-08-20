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

theorem figalli_OT_regularity_pi {n : ℕ}
    (mu nu : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (mu i)] [∀ i, IsFiniteMeasure (nu i)]
    {A B : Fin n → Set ℝ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hmu : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≤ y →
      mu i (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x)))
    (hnu : ∀ i, ∀ u ∈ B i, ∀ v ∈ B i, u ≤ v →
      ENNReal.ofReal (lam * (v - u)) ≤ nu i (Set.Ioc u v))
    {T : Fin n → ℝ → ℝ} (hTB : ∀ i, ∀ x ∈ A i, T i x ∈ B i)
    (hT : ∀ i, ∀ x ∈ A i, cdfReal (nu i) (T i x) = cdfReal (mu i) x) :
    LipschitzOnWith (Real.toNNReal (Lam / lam))
      (fun x : Fin n → ℝ => fun i => T i (x i)) {x : Fin n → ℝ | ∀ i, x i ∈ A i} := by
  have hc : ((Real.toNNReal (Lam / lam) : ℝ≥0) : ℝ) = Lam / lam :=
    Real.coe_toNNReal _ (div_nonneg hLam hlam.le)
  have hnn : (0:ℝ) ≤ Lam / lam := div_nonneg hLam hlam.le
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  rw [hc]
  refine (dist_pi_le_iff (mul_nonneg hnn dist_nonneg)).2 fun i => ?_
  have hi := figalli_OT_regularity_lipschitzOnWith (mu i) (nu i) hlam hLam (hmu i) (hnu i)
    (hTB i) (hT i)
  have h1 : dist (T i (x i)) (T i (y i)) ≤ (Lam / lam) * dist (x i) (y i) := by
    have := hi.dist_le_mul (x i) (hx i) (y i) (hy i)
    rwa [hc] at this
  have h2 : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  calc dist (T i (x i)) (T i (y i)) ≤ (Lam / lam) * dist (x i) (y i) := h1
    _ ≤ (Lam / lam) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]

end Frontier

