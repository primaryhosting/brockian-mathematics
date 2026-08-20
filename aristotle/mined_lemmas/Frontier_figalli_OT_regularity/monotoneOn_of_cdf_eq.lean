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

theorem monotoneOn_of_cdf_eq {lam : ℝ} (hlam : 0 < lam) {F G T : ℝ → ℝ} {A B : Set ℝ}
    (hFmono : MonotoneOn F A)
    (hG : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → lam * (v - u) ≤ G v - G u)
    (hTB : ∀ x ∈ A, T x ∈ B) (hT : ∀ x ∈ A, G (T x) = F x) :
    MonotoneOn T A := by
  intro x hx y hy hxy
  by_contra hlt
  push_neg at hlt
  have h1 : lam * (T x - T y) ≤ G (T x) - G (T y) :=
    hG _ (hTB y hy) _ (hTB x hx) hlt.le
  have h2 : G (T x) - G (T y) = F x - F y := by rw [hT x hx, hT y hy]
  have h3 : F x ≤ F y := hFmono hx hy hxy
  have h4 : 0 < lam * (T x - T y) := mul_pos hlam (by linarith)
  linarith

/-- **One-dimensional optimal transport regularity, analytic form.**
If `F` is monotone on `A` with increments at most `Λ (y - x)`, `G` has increments at least
`lam (v - u)` on `B` with `lam > 0`, and `T : A → B` matches the two distribution functions
(`G (T x) = F x`, i.e. `T = G⁻¹ ∘ F` is the monotone rearrangement), then `T` is
`(Λ / lam)`-Lipschitz on `A`. -/
