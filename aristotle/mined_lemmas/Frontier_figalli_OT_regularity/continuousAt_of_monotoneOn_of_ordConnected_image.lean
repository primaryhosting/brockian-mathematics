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
## Setting

We formalize the one-dimensional base case of the Ma–Trudinger–Wang / Figalli regularity
theory for optimal transport.

The transport cost is the quadratic cost `c x y = (x - y)^2 / 2`.  For this cost Brenier's

theorem continuousAt_of_monotoneOn_of_ordConnected_image {T : ℝ → ℝ} {a r : ℝ} (hr : 0 < r)
    (hmono : MonotoneOn T (Set.Icc (a - r) (a + r)))
    (hoc : (T '' Set.Icc (a - r) (a + r)).OrdConnected) :
    ContinuousAt T a := by
  have ha : a ∈ Set.Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_delta_right hr (half_pos hε) hmono hoc
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_delta_left hr (half_pos hε) hmono hoc
  refine ⟨min (min δ₁ δ₂) r, by positivity, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx ⊢
  have hxr : |x - a| < r := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (le_refl r))
  have hx1 : |x - a| < δ₁ :=
    lt_of_lt_of_le hx (le_trans (min_le_left _ _) (min_le_left _ _))
  have hx2 : |x - a| < δ₂ :=
    lt_of_lt_of_le hx (le_trans (min_le_left _ _) (min_le_right _ _))
  have hxabs := abs_lt.mp hxr
  have hxmem : x ∈ Set.Icc (a - r) (a + r) := ⟨by linarith [hxabs.1], by linarith [hxabs.2]⟩
  rcases le_total a x with hax | hxa
  · have hupper : T x ≤ T a + ε / 2 := by
      refine h₁ x ⟨hax, ?_⟩
      have := (abs_lt.mp hx1).2
      linarith
    have hlower : T a ≤ T x := hmono ha hxmem hax
    rw [abs_lt]
    constructor <;> linarith
  · have hlower : T a - ε / 2 ≤ T x := by
      refine h₂ x ⟨?_, hxa⟩
      have := (abs_lt.mp hx2).1
      linarith
    have hupper : T x ≤ T a := hmono hxmem ha hxa
    rw [abs_lt]
    constructor <;> linarith

/-!
## The regularity theorem
-/

/-- **Interior `C¹` regularity of one-dimensional optimal transport maps** (base case of the
Ma–Trudinger–Wang / Figalli regularity theory).

Setting: the quadratic cost `Frontier.quadraticCost x y = (x - y)^2 / 2` on the line.  By
Brenier's theorem an optimal transport map for this cost is the derivative `T = u'` of a
convex potential `u`; in dimension one the MTW condition holds automatically (the mixed
second derivative of the cost is constant, see `Frontier.quadraticCost_mixed_deriv`).

Conclusion, on an open set `s` on which the Brenier potential `u` is convex and
differentiable (i.e. the transport map is single valued):

* the transport map `T = u'` is monotone on `s` — the one-dimensional form of
  `c`-cyclical monotonicity;
* `T` is continuous on `s`;
* the potential `u` is `C¹` on `s`;
* `T` is optimal for the two-point rearrangement problem: swapping the images of two points
  never decreases the total quadratic cost.
-/
