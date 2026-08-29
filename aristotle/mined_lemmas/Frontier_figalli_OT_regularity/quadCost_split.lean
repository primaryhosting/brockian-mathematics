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

namespace Frontier

/-!
## The quadratic cost and the (degenerate) MTW condition

The Ma–Trudinger–Wang condition is a curvature condition on the mixed fourth
derivatives of the cost `c(x, y)`.  For the quadratic cost
`c(x, y) = ‖x - y‖ ^ 2 / 2` on a real inner product space, the cost splits as a
sum of a function of `x`, a function of `y`, and a *bilinear* cross term
`- ⟪x, y⟫`.  Consequently every mixed derivative of order at least three
vanishes, and the MTW tensor is identically zero: the quadratic cost satisfies
`MTW(0)`, the base case of the Ma–Trudinger–Wang / Figalli theory.

The lemma `Frontier.quadCost_split` records exactly this splitting, with the
cross term exhibited as a genuine continuous bilinear form.
-/

/-- The quadratic optimal-transport cost `c(x, y) = ‖x - y‖ ^ 2 / 2`. -/

theorem quadCost_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∀ x y : E,
      quadCost x y = ‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 + B x y := by
  refine ⟨-(innerSL ℝ), fun x y => ?_⟩
  have h : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    simpa using norm_sub_sq_real x y
  simp only [quadCost, h, ContinuousLinearMap.neg_apply, innerSL_apply_apply]
  ring

/-!
## The one-dimensional base case of optimal transport regularity

In dimension one the Brenier map for the quadratic cost is the monotone
rearrangement: the (essentially unique) optimal map `T` pushing the measure with
density `g` forward to the measure with density `f` is nondecreasing, and it is
characterised by the balance condition

`∫_{T a}^{T b} f = ∫_a^b g`   for all `a ≤ b`.

The base case of the regularity theory then says: if the target density is
bounded below by `lam > 0` and the source density is bounded above by `Lam`,
the transport map is Lipschitz with constant `Lam / lam`.  This is the
elementary model for the higher-dimensional regularity results obtained under
the Ma–Trudinger–Wang condition.

`Frontier.figalli_OT_regularity` below is this statement.
-/

/-- Key quantitative estimate: for `a ≤ b`, the monotone transport map satisfies
`lam * (T b - T a) ≤ Lam * (b - a)`. -/
