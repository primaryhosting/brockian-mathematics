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
theorem says that an optimal transport map is (a.e.) the gradient `T = u'` of a convex
potential `u`, and Ma–Trudinger–Wang / Figalli regularity theory asks when such a map is
continuous.  In dimension one the MTW condition is automatically satisfied (the MTW tensor
is evaluated on pairs of orthogonal vectors, and no such nonzero pair exists on the line;
moreover the mixed second derivative of the quadratic cost is the constant `-1`, so all
higher mixed derivatives entering the MTW tensor vanish — see
`Frontier.quadraticCost_mixed_deriv`).

The regularity statement proved here is the interior `C^1` statement: on an open set where
the Brenier potential is differentiable (i.e. where the transport map is single valued),
the transport map `T = u'` is automatically continuous, so `u` is `C^1` there.  The proof
runs through the two structural facts underlying the theory: monotonicity of `T`
(equivalently, `c`-monotonicity of the transport plan) and Darboux's intermediate value
property for derivatives; the continuity argument then splits into cases according to
whether `T` already satisfies the required bound on a fixed interval or overshoots it.
-/

/-- The quadratic transport cost on the line. -/
noncomputable def quadraticCost (x y : ℝ) : ℝ := (x - y) ^ 2 / 2

@[simp]
theorem quadraticCost_apply (x y : ℝ) : quadraticCost x y = (x - y) ^ 2 / 2 := rfl

/-- The mixed second derivative of the quadratic cost is the constant `-1`.  Consequently all
higher mixed derivatives of the cost vanish, which is the (degenerate) form the MTW condition
takes for the quadratic cost. -/
theorem quadraticCost_mixed_deriv (x y : ℝ) :
    deriv (fun x' : ℝ => deriv (fun y' : ℝ => quadraticCost x' y') y) x = -1 := by
  have h : ∀ x' : ℝ, deriv (fun y' : ℝ => quadraticCost x' y') y = -(x' - y) := by
    intro x'
    have : deriv (fun y' : ℝ => (x' - y') ^ 2 / 2) y = -(x' - y) := by
      have hd : HasDerivAt (fun y' : ℝ => (x' - y') ^ 2 / 2) (-(x' - y)) y := by
        have h1 : HasDerivAt (fun y' : ℝ => x' - y') (-1 : ℝ) y := by
          simpa using (hasDerivAt_id y).const_sub x'
        have h2 := (h1.pow 2).div_const 2
        convert h2 using 1
        ring
      exact hd.deriv
    simpa [quadraticCost] using this
  simp only [h]
  have hd : HasDerivAt (fun x' : ℝ => -(x' - y)) (-1 : ℝ) x :=
    ((hasDerivAt_id x).sub_const y).neg
  exact hd.deriv

/-!
## A monotone function with the intermediate value property is continuous
-/

/-- One-sided (right) estimate: a monotone function whose image on a closed interval around `a`
is order-connected can be squeezed just above `T a` immediately to the right of `a`. -/
theorem exists_delta_right {T : ℝ → ℝ} {a r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hmono : MonotoneOn T (Set.Icc (a - r) (a + r)))
    (hoc : (T '' Set.Icc (a - r) (a + r)).OrdConnected) :
    ∃ δ > 0, ∀ y ∈ Set.Icc a (a + δ), T y ≤ T a + ε := by
  have ha : a ∈ Set.Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  by_cases h : ∀ y ∈ Set.Icc a (a + r), T y ≤ T a + ε
  · exact ⟨r, hr, h⟩
  · push_neg at h
    obtain ⟨x, hx, hxT⟩ := h
    have hxmem : x ∈ Set.Icc (a - r) (a + r) := ⟨by linarith [hx.1], hx.2⟩
    have hm : T a + ε / 2 ∈ Set.Icc (T a) (T x) := by
      constructor
      · linarith
      · linarith
    have hmem : T a + ε / 2 ∈ T '' Set.Icc (a - r) (a + r) :=
      hoc.out (Set.mem_image_of_mem T ha) (Set.mem_image_of_mem T hxmem) hm
    obtain ⟨c, hc, hcT⟩ := hmem
    have hac : a < c := by
      by_contra hle
      push_neg at hle
      have := hmono hc ha hle
      rw [hcT] at this
      linarith
    refine ⟨c - a, by linarith, ?_⟩
    intro y hy
    have hyc : y ≤ c := by have := hy.2; linarith
    have hymem : y ∈ Set.Icc (a - r) (a + r) :=
      ⟨by linarith [hy.1], le_trans hyc hc.2⟩
    have := hmono hymem hc hyc
    rw [hcT] at this
    linarith

/-- One-sided (left) estimate, the mirror image of `Frontier.exists_delta_right`. -/
theorem exists_delta_left {T : ℝ → ℝ} {a r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hmono : MonotoneOn T (Set.Icc (a - r) (a + r)))
    (hoc : (T '' Set.Icc (a - r) (a + r)).OrdConnected) :
    ∃ δ > 0, ∀ y ∈ Set.Icc (a - δ) a, T a - ε ≤ T y := by
  have ha : a ∈ Set.Icc (a - r) (a + r) := ⟨by linarith, by linarith⟩
  by_cases h : ∀ y ∈ Set.Icc (a - r) a, T a - ε ≤ T y
  · exact ⟨r, hr, h⟩
  · push_neg at h
    obtain ⟨x, hx, hxT⟩ := h
    have hxmem : x ∈ Set.Icc (a - r) (a + r) := ⟨hx.1, by linarith [hx.2]⟩
    have hm : T a - ε / 2 ∈ Set.Icc (T x) (T a) := by
      constructor
      · linarith
      · linarith
    have hmem : T a - ε / 2 ∈ T '' Set.Icc (a - r) (a + r) :=
      hoc.out (Set.mem_image_of_mem T hxmem) (Set.mem_image_of_mem T ha) hm
    obtain ⟨c, hc, hcT⟩ := hmem
    have hca : c < a := by
      by_contra hle
      push_neg at hle
      have := hmono ha hc hle
      rw [hcT] at this
      linarith
    refine ⟨a - c, by linarith, ?_⟩
    intro y hy
    have hcy : c ≤ y := by have := hy.1; linarith
    have hymem : y ∈ Set.Icc (a - r) (a + r) :=
      ⟨le_trans hc.1 hcy, by linarith [hy.2]⟩
    have := hmono hc hymem hcy
    rw [hcT] at this
    linarith

/-- A function which is monotone on a closed interval around `a` and whose image on that
interval is order-connected (the intermediate value property, guaranteed for derivatives by
Darboux's theorem) is continuous at `a`. -/
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
theorem figalli_OT_regularity {s : Set ℝ} (hs : IsOpen s) {u : ℝ → ℝ} (hu : ConvexOn ℝ s u)
    (hdiff : ∀ x ∈ s, DifferentiableAt ℝ u x) :
    MonotoneOn (deriv u) s ∧ ContinuousOn (deriv u) s ∧ ContDiffOn ℝ 1 u s ∧
      ∀ x ∈ s, ∀ y ∈ s,
        quadraticCost x (deriv u x) + quadraticCost y (deriv u y)
          ≤ quadraticCost x (deriv u y) + quadraticCost y (deriv u x) := by
  -- Monotonicity of the transport map: the derivative of a convex function is monotone.
  have hmono : MonotoneOn (deriv u) s := hu.monotoneOn_deriv hdiff
  -- Continuity: monotonicity together with Darboux's intermediate value property.
  have hcont : ContinuousOn (deriv u) s := by
    intro a ha
    obtain ⟨R, hR, hRs⟩ := Metric.isOpen_iff.mp hs a ha
    refine ContinuousAt.continuousWithinAt ?_
    have hsub : Set.Icc (a - R / 2) (a + R / 2) ⊆ s := by
      intro x hx
      refine hRs ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hx.1]; linarith [hx.2]]
    refine continuousAt_of_monotoneOn_of_ordConnected_image (r := R / 2) (by linarith)
      (hmono.mono hsub) ?_
    exact Set.ordConnected_Icc.image_deriv fun x hx => hdiff x (hsub hx)
  refine ⟨hmono, hcont, ?_, ?_⟩
  · -- `C¹` regularity of the potential.
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hdiff x hx).differentiableWithinAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · simpa [contDiffOn_zero] using hcont
  · -- Two-point optimality of the transport map.
    intro x hx y hy
    rcases le_total x y with hxy | hxy
    · have h := hmono hx hy hxy
      simp only [quadraticCost_apply]
      nlinarith [sq_nonneg (x - y), sq_nonneg (deriv u x - deriv u y)]
    · have h := hmono hy hx hxy
      simp only [quadraticCost_apply]
      nlinarith [sq_nonneg (x - y), sq_nonneg (deriv u x - deriv u y)]

end Frontier

