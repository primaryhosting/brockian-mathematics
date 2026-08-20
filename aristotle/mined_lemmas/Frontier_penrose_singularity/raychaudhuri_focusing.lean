import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, so the header comment
-- above is placed immediately after the single `import Mathlib` line.)

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The analytic core: Raychaudhuri focusing

For a null geodesic congruence with vanishing shear and rotation (as holds for the
generators of the boundary of the causal future of a surface), the Raychaudhuri equation
together with the null energy condition `Ric(k,k) ≥ 0` gives the differential inequality

  `θ' ≤ - θ² / 2`

for the expansion `θ` as a function of the affine parameter. The following theorem is the
exact analytic content of the focusing argument: a solution of this inequality with
`θ 0 < 0` blows up (i.e. cannot be continued) before affine parameter `2 / |θ 0|`.
-/

/-- **Raychaudhuri focusing theorem.**  If `θ` satisfies the null-energy-condition
inequality `θ' ≤ -θ²/2` on `[0, L]` and starts out converging, `θ 0 < 0`, then
`L < 2 / (-θ 0)`.  Equivalently: a congruence with initially negative expansion develops a
focal point within affine parameter `2 / |θ 0|`. -/

theorem raychaudhuri_focusing {L : ℝ} (θ dθ : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt θ (dθ t) t)
    (hNEC : ∀ t ∈ Set.Icc (0 : ℝ) L, dθ t ≤ -(θ t) ^ 2 / 2)
    (hinit : θ 0 < 0) : L < 2 / (-θ 0) := by
  rcases le_or_gt L 0 with hL | hL
  · exact lt_of_le_of_lt hL (div_pos (by norm_num) (by linarith))
  -- `θ` is nonincreasing on `[0, L]`, hence stays `≤ θ 0 < 0`.
  have hderiv' : ∀ x ∈ interior (Set.Icc (0 : ℝ) L), HasDerivAt θ (dθ x) x := by
    intro x hx
    rw [interior_Icc] at hx
    exact hderiv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcont : ContinuousOn θ (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn θ (Set.Icc (0 : ℝ) L) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := dθ) (convex_Icc _ _) hcont
      (fun x hx => (hderiv' x hx).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have := hNEC x hx'
    nlinarith [sq_nonneg (θ x)]
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) L, θ t < 0 := fun t ht =>
    lt_of_le_of_lt (hanti (Set.left_mem_Icc.mpr (le_of_lt hL)) ht ht.1) hinit
  -- The reciprocal `f = 1/θ` grows at least at rate `1/2`.
  set f : ℝ → ℝ := fun t => (θ t)⁻¹ with hf
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt f (-dθ t / (θ t) ^ 2) t := by
    intro t ht
    have h0 : θ t ≠ 0 := ne_of_lt (hneg t ht)
    simpa [hf, neg_div] using (hderiv t ht).inv h0
  have hfgrow : ∀ t ∈ Set.Icc (0 : ℝ) L, (1 : ℝ) / 2 ≤ -dθ t / (θ t) ^ 2 := by
    intro t ht
    have h0 : (0 : ℝ) < (θ t) ^ 2 := by
      have h := hneg t ht; nlinarith
    rw [le_div_iff₀ h0]
    have := hNEC t ht
    linarith
  have hcontf : ContinuousOn f (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hfderiv t ht).continuousAt.continuousWithinAt
  -- Hence `g t = f t - t/2` is monotone on `[0, L]`.
  have hgmono : MonotoneOn (fun t => f t - t / 2) (Set.Icc (0 : ℝ) L) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) L)
      (f' := fun t => -dθ t / (θ t) ^ 2 - 1 / 2)
      (hcontf.sub (continuousOn_id.div_const 2))
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (((hfderiv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).sub
        ((hasDerivAt_id x).div_const 2)).hasDerivWithinAt)
    · rw [interior_Icc] at hx
      have := hfgrow x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      linarith
  have hmain : f 0 + L / 2 ≤ f L := by
    have := hgmono (Set.left_mem_Icc.mpr (le_of_lt hL))
      (Set.right_mem_Icc.mpr (le_of_lt hL)) (le_of_lt hL)
    simp only [zero_div, sub_zero] at this
    linarith
  have hfL : f L < 0 := inv_neg''.mpr (hneg L (Set.right_mem_Icc.mpr (le_of_lt hL)))
  have hpos : (0 : ℝ) < -θ 0 := by linarith
  have hf0 : f 0 = -(1 / (-θ 0)) := by
    simp only [hf]
    field_simp
  rw [hf0] at hmain
  have h2 : L / 2 < 1 / (-θ 0) := by linarith
  rw [lt_div_iff₀ hpos] at h2
  rw [lt_div_iff₀ hpos]
  linarith

/-!
## The geometric setting

Mathlib does not (yet) contain Lorentzian causal theory — no `J⁺`, no achronal boundaries,
no null geodesic congruences.  We therefore package the geometric input of Penrose's
