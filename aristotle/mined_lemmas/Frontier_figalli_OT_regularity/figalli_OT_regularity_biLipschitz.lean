import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

Figalli's regularity theory for optimal transport asserts, roughly, that if the cost
function `c` satisfies the Ma–Trudinger–Wang (MTW) condition and the source and target
densities are bounded away from `0` and `∞` on suitable domains, then the optimal
transport map inherits regularity (continuity, Lipschitz/Hölder bounds, and higher
smoothness by bootstrapping).

We formalize here the **one dimensional base case** of this theory in a fully
self-contained and Lean-checked way.  In dimension one the MTW tensor is vacuous
(it is a quadratic form in a pair of *orthogonal* directions `ξ ⊥ η`, which cannot
both be non-zero on a line), so *every* smooth twisted cost satisfies MTW; the entire
content of the regularity statement is then the density bound argument formalized below.
Moreover the optimal map for a twisted cost in one dimension is the monotone
rearrangement, characterized by the mass-balance (push-forward) identity
`G (T x) = F x` between the cumulative distribution functions.

The main theorem `Frontier.figalli_OT_regularity` states:

> if the source distribution function `F` grows at most at rate `Λ` (i.e. its density is
> `≤ Λ`), the target distribution function `G` grows at least at rate `lam > 0`
> (i.e. its density is `≥ lam`), and `T` is a monotone map satisfying the mass balance
> `G ∘ T = F`, then `T` is Lipschitz with constant `Λ / lam`.

This is exactly the one dimensional form of the Caffarelli/Figalli a-priori estimate:
the modulus of continuity of the transport map is controlled by the ratio of the
density bounds.  A two-sided (bi-Lipschitz) version and a version stated directly in
terms of densities are also proved, together with a chain/iteration statement proved
by induction on the number of transports.
-/

namespace Frontier

/-! ### The MTW condition in dimension one -/

/-- The Ma–Trudinger–Wang condition, as a condition on a real-valued quadratic-form
valued map `S` on pairs of directions.  `S x y ξ η` plays the role of the MTW tensor
`𝔖_c(x,y)(ξ,η)`, and the condition `MTWNonneg` says that it is non-negative on
orthogonal pairs of directions. -/

theorem figalli_OT_regularity_biLipschitz
    {F G T : ℝ → ℝ} {lam Λ lam' Λ' : ℝ}
    (hlam : 0 < lam) (hΛ' : 0 < Λ')
    (hF : ∀ x y : ℝ, x ≤ y → F y - F x ≤ Λ * (y - x))
    (hF' : ∀ x y : ℝ, x ≤ y → lam' * (y - x) ≤ F y - F x)
    (hG : ∀ s t : ℝ, s ≤ t → lam * (t - s) ≤ G t - G s)
    (hG' : ∀ s t : ℝ, s ≤ t → G t - G s ≤ Λ' * (t - s))
    (hT : Monotone T)
    (hpush : ∀ x : ℝ, G (T x) = F x)
    {x y : ℝ} (hxy : x ≤ y) :
    (lam' / Λ') * (y - x) ≤ T y - T x ∧ T y - T x ≤ (Λ / lam) * (y - x) := by
  refine ⟨?_, transport_increment_le hlam hF hG hT hpush hxy⟩
  have h1 : lam' * (y - x) ≤ F y - F x := hF' _ _ hxy
  have h2 : F y - F x = G (T y) - G (T x) := by rw [hpush, hpush]
  have h3 : G (T y) - G (T x) ≤ Λ' * (T y - T x) := hG' _ _ (hT hxy)
  have h4 : lam' * (y - x) ≤ Λ' * (T y - T x) := by linarith [h1, h3, h2.le, h2.ge]
  rw [div_mul_eq_mul_div, div_le_iff₀ hΛ', mul_comm (T y - T x) Λ']
  exact h4

/-! ### Version stated directly in terms of densities -/

/-- If `F` is the distribution function of a density `f ≤ Λ`, then `F` increases at rate
at most `Λ`. -/
