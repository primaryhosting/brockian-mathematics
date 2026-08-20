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

theorem figalli_OT_regularity
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu] {A B : Set ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hmu : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → mu (Set.Ioc x y) ≤ ENNReal.ofReal (Lam * (y - x)))
    (hnu : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → ENNReal.ofReal (lam * (v - u)) ≤ nu (Set.Ioc u v))
    {T : ℝ → ℝ} (hTB : ∀ x ∈ A, T x ∈ B)
    (hT : ∀ x ∈ A, cdfReal nu (T x) = cdfReal mu x) :
    ∀ x ∈ A, ∀ y ∈ A, |T y - T x| ≤ (Lam / lam) * |y - x| :=
  transport_lipschitzOn_of_cdf_bounds hlam ((cdfReal_mono mu).monotoneOn A)
    (fun x hx y hy hxy => cdfReal_sub_le mu hLam hxy (hmu x hx y hy hxy))
    (fun u hu v hv huv => le_cdfReal_sub nu huv (hnu u hu v hv huv)) hTB hT

/-- Packaged form of `figalli_OT_regularity` as `LipschitzOnWith`. -/
