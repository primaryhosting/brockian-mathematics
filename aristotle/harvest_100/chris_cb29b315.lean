/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

open Set

/-!
## The Raychaudhuri focusing theorem

The analytic heart of Penrose's singularity theorem is the following statement about the
expansion `θ` of a null geodesic congruence, as a function of the affine parameter `t`.

Along a hypersurface-orthogonal null geodesic congruence with tangent field `k`, the
Raychaudhuri equation reads

  `dθ/dt = -θ²/2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`,

where `σ_{ab}σ^{ab} ≥ 0` is the squared shear (the twist vanishes by hypersurface
orthogonality) and `R_{ab} k^a k^b ≥ 0` is the null energy condition (via the Einstein
equations, equivalently the null convergence condition).

Consequently `dθ/dt ≤ -θ²/2`, and if the congruence starts on a *trapped surface*, i.e.
`θ 0 < 0`, then `θ` reaches `-∞` (a focal point) within affine parameter `2/|θ 0|`.
So the congruence cannot be defined on any longer affine interval: the null geodesics are
incomplete (or hit a focal point, which in Penrose's global argument is what contradicts
the existence of a noncompact Cauchy surface).
-/

/-- **Focusing lemma.** If the expansion `θ` of a null congruence is defined and
differentiable on the affine interval `[0, L]` and satisfies the Raychaudhuri inequality
`θ' ≤ -θ²/2` there, and if the initial cross-section is trapped (`θ 0 < 0`), then
`L < 2 / |θ 0|`.  In particular no such congruence survives past affine parameter
`2 / |θ 0|`. -/
theorem raychaudhuri_focusing (expansion expansionDeriv : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt expansion (expansionDeriv t) t)
    (hray : ∀ t ∈ Icc (0 : ℝ) L, expansionDeriv t ≤ -(expansion t) ^ 2 / 2)
    (htrapped : expansion 0 < 0) : L < 2 / (-expansion 0) := by
  have hcont : ContinuousOn expansion (Icc 0 L) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hint : interior (Icc (0 : ℝ) L) ⊆ Icc 0 L := by
    rw [interior_Icc]; exact Ioo_subset_Icc_self
  -- The expansion is nonincreasing, hence stays negative.
  have hanti : AntitoneOn expansion (Icc 0 L) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 L) hcont
    · exact fun t ht => ((hderiv t (hint ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [(hderiv t (hint ht)).deriv]
      have := hray t (hint ht)
      nlinarith [sq_nonneg (expansion t)]
  have hneg : ∀ t ∈ Icc (0 : ℝ) L, expansion t < 0 := by
    intro t ht
    have := hanti (left_mem_Icc.2 hL) ht ht.1
    linarith
  -- `t ↦ 1/θ t - t/2` is nondecreasing.
  set g : ℝ → ℝ := fun t => (expansion t)⁻¹ - t / 2 with hg
  have hgderiv : ∀ t ∈ Icc (0 : ℝ) L,
      HasDerivAt g (-(expansionDeriv t) / (expansion t) ^ 2 - 1 / 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => (expansion t)⁻¹)
        (-(expansionDeriv t) / (expansion t) ^ 2) t :=
      (hderiv t ht).inv (ne_of_lt (hneg t ht))
    have h2 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    exact h1.sub h2
  have hmono : MonotoneOn g (Icc 0 L) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 L)
      (fun t ht => ((hgderiv t ht).continuousAt).continuousWithinAt)
      (fun t ht => ((hgderiv t (hint ht)).differentiableAt).differentiableWithinAt)
    intro t ht
    rw [(hgderiv t (hint ht)).deriv]
    have hn := hneg t (hint ht)
    have hr := hray t (hint ht)
    have hsq : 0 < (expansion t) ^ 2 := by nlinarith
    rw [sub_nonneg, le_div_iff₀ hsq]
    linarith
  have hkey := hmono (left_mem_Icc.2 hL) (right_mem_Icc.2 hL) hL
  have hLneg : (expansion L)⁻¹ < 0 := inv_neg''.2 (hneg L (right_mem_Icc.2 hL))
  simp only [hg] at hkey
  have ha : (0 : ℝ) < -expansion 0 := by linarith
  have hinv : (expansion 0)⁻¹ = -(-expansion 0)⁻¹ := by field_simp
  have hcancel : (-expansion 0) * (-expansion 0)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  rw [lt_div_iff₀ ha]
  norm_num at hkey
  nlinarith [hkey, hLneg, hinv, hcancel]

/-- Data of a *complete* hypersurface-orthogonal null geodesic congruence emanating
orthogonally from a smooth codimension-two spacelike surface in a spacetime.

`expansion t` is the expansion `θ` of the congruence at affine parameter `t`,
`shearSq t = σ_{ab}σ^{ab} ≥ 0` is its squared shear, and `ricciNull t = R_{ab} k^a k^b`
is the null-null Ricci curvature along the generators.

Null geodesic *completeness* is encoded by the requirement that the data be defined and
the expansion differentiable for **all** affine parameters `t ≥ 0`, with the Raychaudhuri
equation holding throughout. -/
structure CompleteNullCongruence where
  /-- Expansion `θ` of the congruence as a function of the affine parameter. -/
  expansion : ℝ → ℝ
  /-- The affine-parameter derivative `dθ/dt` of the expansion. -/
  expansionDeriv : ℝ → ℝ
  /-- Squared shear `σ_{ab}σ^{ab}` of the congruence. -/
  shearSq : ℝ → ℝ
  /-- Null-null Ricci curvature `R_{ab}k^a k^b` along the generators. -/
  ricciNull : ℝ → ℝ
  /-- Completeness: the expansion is differentiable at every affine parameter `t ≥ 0`. -/
  hasDerivAt_expansion : ∀ t ∈ Ici (0 : ℝ), HasDerivAt expansion (expansionDeriv t) t
  /-- The Raychaudhuri equation for a hypersurface-orthogonal null congruence
  (vanishing twist). -/
  raychaudhuri : ∀ t ∈ Ici (0 : ℝ),
    expansionDeriv t = -(expansion t) ^ 2 / 2 - shearSq t - ricciNull t
  /-- The squared shear of a real congruence is nonnegative. -/
  shearSq_nonneg : ∀ t : ℝ, 0 ≤ shearSq t

/-- The **null energy condition** (null convergence condition) for a congruence:
`R_{ab} k^a k^b ≥ 0` along the generators. -/
def CompleteNullCongruence.NullEnergyCondition (C : CompleteNullCongruence) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), 0 ≤ C.ricciNull t

/-- The initial cross-section of the congruence is **trapped**: the outgoing null
expansion is negative at `t = 0`. -/
def CompleteNullCongruence.Trapped (C : CompleteNullCongruence) : Prop :=
  C.expansion 0 < 0

/-- **Penrose singularity theorem (focusing form).**

A spacetime containing a trapped surface and satisfying the null energy condition is null
geodesically incomplete: there is no null geodesic congruence orthogonal to the trapped
surface that is complete (defined for all affine parameters `t ≥ 0`) and obeys the
Raychaudhuri equation with nonnegative shear and nonnegative null-null Ricci curvature.

This is the contrapositive formulation: the assumptions of completeness, the null energy
condition, and the existence of a trapped cross-section are jointly contradictory.  The
proof is the Raychaudhuri focusing estimate `raychaudhuri_focusing`: the expansion must
blow up before affine parameter `2/|θ 0|`, so the congruence cannot extend that far. -/
theorem penrose_singularity (C : CompleteNullCongruence)
    (hNEC : C.NullEnergyCondition) (htrapped : C.Trapped) : False := by
  -- Take an affine interval longer than the focusing bound `2/|θ 0|`.
  set L : ℝ := 2 / (-C.expansion 0) + 1 with hLdef
  have hpos : (0 : ℝ) < -C.expansion 0 := by
    have := htrapped; unfold CompleteNullCongruence.Trapped at this; linarith
  have hL : 0 ≤ L := by
    have : 0 < 2 / (-C.expansion 0) := by positivity
    simp only [hLdef]; linarith
  have hsub : Icc (0 : ℝ) L ⊆ Ici (0 : ℝ) := fun t ht => ht.1
  have hbound : L < 2 / (-C.expansion 0) := by
    refine raychaudhuri_focusing C.expansion C.expansionDeriv L hL
      (fun t ht => C.hasDerivAt_expansion t (hsub ht)) (fun t ht => ?_) htrapped
    have hr := C.raychaudhuri t (hsub ht)
    have hs := C.shearSq_nonneg t
    have hn := hNEC t (hsub ht)
    linarith
  simp only [hLdef] at hbound
  linarith

/-- Non-vacuity check: the hypotheses of `penrose_singularity` are not contradictory on their
own.  A complete, shear-free, vacuum congruence with vanishing expansion satisfies the null
energy condition (it is only the *trapped* condition that forces the contradiction). -/
example : ∃ C : CompleteNullCongruence, C.NullEnergyCondition ∧ ¬ C.Trapped := by
  refine ⟨{ expansion := fun _ => 0, expansionDeriv := fun _ => 0, shearSq := fun _ => 0,
            ricciNull := fun _ => 0,
            hasDerivAt_expansion := fun t _ => hasDerivAt_const t 0,
            raychaudhuri := by intro t _; norm_num,
            shearSq_nonneg := fun _ => le_rfl }, fun t _ => le_rfl, ?_⟩
  simp [CompleteNullCongruence.Trapped]

end Frontier

