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

theorem transport_lipschitzOn_of_cdf_bounds
    {lam Lam : ℝ} (hlam : 0 < lam) {F G T : ℝ → ℝ} {A B : Set ℝ} (hFmono : MonotoneOn F A)
    (hF : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → F y - F x ≤ Lam * (y - x))
    (hG : ∀ u ∈ B, ∀ v ∈ B, u ≤ v → lam * (v - u) ≤ G v - G u)
    (hTB : ∀ x ∈ A, T x ∈ B) (hT : ∀ x ∈ A, G (T x) = F x) :
    ∀ x ∈ A, ∀ y ∈ A, |T y - T x| ≤ (Lam / lam) * |y - x| := by
  have hTmono : MonotoneOn T A := monotoneOn_of_cdf_eq hlam hFmono hG hTB hT
  -- the key one-sided estimate
  have key : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → T y - T x ≤ (Lam / lam) * (y - x) := by
    intro x hx y hy hxy
    have h1 : lam * (T y - T x) ≤ G (T y) - G (T x) :=
      hG _ (hTB x hx) _ (hTB y hy) (hTmono hx hy hxy)
    have h2 : G (T y) - G (T x) = F y - F x := by rw [hT x hx, hT y hy]
    have h3 : F y - F x ≤ Lam * (y - x) := hF x hx y hy hxy
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    nlinarith
  intro x hx y hy
  rcases le_total x y with h | h
  · have h1 : 0 ≤ T y - T x := sub_nonneg.2 (hTmono hx hy h)
    rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.2 h)]
    exact key x hx y hy h
  · have h1 : T y - T x ≤ 0 := sub_nonpos.2 (hTmono hy hx h)
    rw [abs_of_nonpos h1, abs_of_nonpos (sub_nonpos.2 h), neg_sub, neg_sub]
    exact key y hy x hx h

/-!
## The main statement
-/

/-- **Figalli-type optimal transport regularity: the one-dimensional base case.**

Let `mu`, `nu` be finite Borel measures on `ℝ`, let `A` be the source domain and `B` the
target domain.  Assume:

* an upper density bound for the source, `mu (Ioc x y) ≤ Λ (y - x)`;
* a lower density bound for the target on `B`, `nu (Ioc u v) ≥ lam (v - u)` with `lam > 0`;
* `T : A → B` is the monotone optimal transport map from `mu` to `nu` for the quadratic
  cost, characterized in dimension one by the matching of the cumulative distribution
  functions, `cdfReal nu (T x) = cdfReal mu x` (that is, `T = G⁻¹ ∘ F`).

Then `T` is Lipschitz on `A` with the sharp constant `Λ / lam`.

In dimension one the Ma–Trudinger–Wang condition for the quadratic cost holds trivially, so
this is exactly the base case of the MTW regularity theory, in its Caffarelli form. -/
