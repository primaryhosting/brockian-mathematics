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
theorem as a structure whose fields are exactly the standard hypotheses of the theorem,
transported to the null generators of the boundary `∂J⁺(S)` of the causal future of a
trapped surface `S`:

* `Gen` is the (nonempty) set of null generators of `∂J⁺(S)` issuing from the trapped
  surface `S`, parametrised by affine parameter `t ≥ 0`;
* `Extends s T` says that the generator `s`, as a generator of the boundary, extends to
  affine parameter `T`;
* `theta s` is the expansion of the congruence along the generator `s`, with derivative
  `dtheta s` with respect to the affine parameter;
* `trapped` is the *trapped surface* hypothesis: the expansion of the outgoing null
  congruence is uniformly negative on the (compact) surface `S`, `θ ≤ -c < 0`;
* `nec` is the Raychaudhuri equation combined with the *null energy condition*
  `Ric(k,k) ≥ 0` (and vanishing rotation for hypersurface-orthogonal generators):
  `θ' = -θ²/2 - σ² - Ric(k,k) ≤ -θ²/2`.

Null geodesic completeness of the spacetime means that every generator can be extended to
arbitrarily large affine parameter while remaining a generator of the achronal boundary
(no generator meets a focal point, since a generator leaves the boundary at a focal point,
and the boundary is generated by inextendible null geodesics as long as they exist).
-/

/-- Abstract data of the null generators of the boundary of the causal future of a
trapped surface in a spacetime satisfying the null energy condition. -/
structure TrappedSurfaceCongruence where
  /-- The null generators of `∂J⁺(S)` emanating from the trapped surface `S`. -/
  Gen : Type
  /-- A trapped surface is nonempty. -/
  gen_nonempty : Nonempty Gen
  /-- `Extends s T` : the generator `s` extends (as a null geodesic generator of the
  boundary) to affine parameter `T`. -/
  Extends : Gen → ℝ → Prop
  /-- The expansion of the congruence along a generator, as a function of the affine
  parameter. -/
  theta : Gen → ℝ → ℝ
  /-- The affine-parameter derivative of the expansion. -/
  dtheta : Gen → ℝ → ℝ
  /-- The expansion is differentiable along the part of a generator that exists. -/
  hasDerivAt_theta : ∀ (s : Gen) (T : ℝ), Extends s T →
    ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt (theta s) (dtheta s t) t
  /-- The uniform bound on the expansion of the trapped surface. -/
  focusConst : ℝ
  /-- Compactness of the trapped surface makes the bound on its expansion uniform. -/
  focusConst_pos : 0 < focusConst
  /-- **Trapped surface hypothesis**: the outgoing null expansion is negative on `S`. -/
  trapped : ∀ s : Gen, theta s 0 ≤ -focusConst
  /-- **Null energy condition** via the Raychaudhuri equation. -/
  nec : ∀ (s : Gen) (T : ℝ), Extends s T →
    ∀ t ∈ Set.Icc (0 : ℝ) T, dtheta s t ≤ -(theta s t) ^ 2 / 2

/-- Null geodesic completeness: every generator of the boundary extends to every
nonnegative affine parameter. -/
def NullGeodesicallyComplete (C : TrappedSurfaceCongruence) : Prop :=
  ∀ (s : C.Gen) (T : ℝ), 0 ≤ T → C.Extends s T

/-- Null geodesic incompleteness: some generator of the boundary fails to extend to some
nonnegative affine parameter. -/
def NullGeodesicallyIncomplete (C : TrappedSurfaceCongruence) : Prop :=
  ∃ (s : C.Gen) (T : ℝ), 0 ≤ T ∧ ¬ C.Extends s T

/-- **Quantitative Penrose bound.**  Every generator of the boundary of the causal future
of a trapped surface terminates before affine parameter `2 / c`, where `-c` bounds the
expansion of the trapped surface. -/
theorem affineLength_lt_of_extends (C : TrappedSurfaceCongruence) {s : C.Gen} {T : ℝ}
    (hT : C.Extends s T) : T < 2 / C.focusConst := by
  have hinit : C.theta s 0 < 0 :=
    lt_of_le_of_lt (C.trapped s) (by simpa using neg_neg_iff_pos.mpr C.focusConst_pos)
  have h := raychaudhuri_focusing (L := T) (C.theta s) (C.dtheta s)
    (C.hasDerivAt_theta s T hT) (C.nec s T hT) hinit
  have hc : C.focusConst ≤ -C.theta s 0 := by
    have := C.trapped s; linarith
  have : 2 / (-C.theta s 0) ≤ 2 / C.focusConst :=
    div_le_div_of_nonneg_left (by norm_num) C.focusConst_pos hc
  linarith

/-- **Penrose singularity theorem** (reduction to the focusing argument).

A spacetime containing a (compact) trapped surface and satisfying the null energy
condition is null geodesically incomplete: the null generators of the boundary of the
causal future of the trapped surface cannot all be extended to arbitrary affine parameter.
The proof is the Raychaudhuri focusing argument: the negative initial expansion of the
trapped surface, together with the null energy condition, forces a focal point within
affine parameter `2 / c`. -/
theorem penrose_singularity (C : TrappedSurfaceCongruence) :
    ¬ NullGeodesicallyComplete C := by
  intro hcomplete
  obtain ⟨s⟩ := C.gen_nonempty
  have hpos : 0 < 2 / C.focusConst := div_pos (by norm_num) C.focusConst_pos
  have hT : C.Extends s (2 / C.focusConst) := hcomplete s _ (le_of_lt hpos)
  exact absurd (affineLength_lt_of_extends C hT) (lt_irrefl _)

/-- Restatement: such a spacetime is null geodesically incomplete. -/
theorem penrose_singularity' (C : TrappedSurfaceCongruence) :
    NullGeodesicallyIncomplete C := by
  obtain ⟨s⟩ := C.gen_nonempty
  refine ⟨s, 2 / C.focusConst, le_of_lt (div_pos (by norm_num) C.focusConst_pos), ?_⟩
  intro hT
  exact absurd (affineLength_lt_of_extends C hT) (lt_irrefl _)

/-!
## Non-vacuity and sharpness

The hypotheses of `TrappedSurfaceCongruence` are satisfiable: the exact solution
`θ t = 2 / (t - 1)` of `θ' = -θ²/2` with `θ 0 = -2` models a congruence focusing exactly
at affine parameter `1 = 2 / focusConst`.  This also shows the bound
`affineLength_lt_of_extends` is sharp.
-/

/-- An explicit congruence satisfying all hypotheses, focusing exactly at affine
parameter `1`. -/
noncomputable def modelCongruence : TrappedSurfaceCongruence where
  Gen := Unit
  gen_nonempty := ⟨()⟩
  Extends := fun _ T => T < 1
  theta := fun _ t => 2 / (t - 1)
  dtheta := fun _ t => -2 / (t - 1) ^ 2
  hasDerivAt_theta := by
    rintro ⟨⟩ T hT t ht
    have h : t - 1 ≠ 0 := by
      have := ht.2
      intro h; apply absurd hT; push_neg; nlinarith
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have h2 := (h1.inv h).const_mul (2 : ℝ)
    have hfun : (fun u : ℝ => 2 * ((fun t : ℝ => t - 1) u)⁻¹) = fun u : ℝ => 2 / (u - 1) := by
      funext u; rw [div_eq_mul_inv]
    rw [show (fun u : ℝ => 2 * (fun t : ℝ => t - 1)⁻¹ u) = fun u : ℝ => 2 / (u - 1) from hfun]
      at h2
    convert h2 using 1
    field_simp
  focusConst := 2
  focusConst_pos := by norm_num
  trapped := by rintro ⟨⟩; norm_num
  nec := by
    rintro ⟨⟩ T hT t ht
    have h : t - 1 ≠ 0 := by
      have := ht.2
      intro h; apply absurd hT; push_neg; nlinarith
    have key : -(2:ℝ) / (t - 1) ^ 2 = -(2 / (t - 1)) ^ 2 / 2 := by
      field_simp
    exact le_of_eq key

example : ¬ NullGeodesicallyComplete modelCongruence := penrose_singularity _

/-- Sharpness: the model congruence does extend to every affine parameter strictly below
the Penrose bound `2 / focusConst = 1`. -/
example (T : ℝ) (hT : T < 2 / modelCongruence.focusConst) : modelCongruence.Extends () T := by
  norm_num [modelCongruence] at hT ⊢
  exact hT

#print axioms Frontier.raychaudhuri_focusing
#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_singularity'

end Frontier

