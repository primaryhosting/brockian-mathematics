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

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity
theorem is formalised here at the level of its analytic core, the *Raychaudhuri
focusing argument*, which is where the null energy condition and the trapped-surface
hypothesis actually enter.

Consider the congruence of future-directed null geodesics orthogonal to a smooth
closed spacelike surface `S`, parametrised by an affine parameter `t ≥ 0`, and let
`theta t` be the expansion of the congruence at affine parameter `t`.  The
Raychaudhuri equation for a hypersurface-orthogonal (hence vorticity-free) null
congruence in a `4`-dimensional spacetime reads

  `theta' = -theta ^ 2 / 2 - shear ^ 2 - Ric(k, k)`,

where `k` is the null tangent.  The null energy condition gives `Ric(k, k) ≥ 0` and
the shear term is a sum of squares, so the whole physical input is captured by the
differential inequality

  `theta' ≤ -theta ^ 2 / 2`.

`S` being a *trapped surface* means precisely that the initial expansion of the
(outgoing as well as ingoing) orthogonal null congruence is negative, `theta 0 < 0`.

The theorem below shows that these hypotheses force the affine parameter range of
the congruence to be *bounded*, by `-2 / theta 0`: a conjugate point (a focal point
of `S`) is reached at or before that affine parameter, so the null geodesics of the
congruence cannot be extended to arbitrarily large affine parameter, i.e. the
spacetime is null geodesically incomplete.
-/

/-- The expansion data of the future-directed null geodesic congruence orthogonal to a
closed spacelike surface, defined on the affine parameter interval `[0, L)`.

* `theta t` is the expansion at affine parameter `t`;
* `dtheta t` is its derivative;
* `raychaudhuri` is the Raychaudhuri equation combined with the null energy condition
  and vanishing vorticity: `theta' ≤ -theta ^ 2 / 2`. -/
structure NullCongruence (L : ℝ) where
  /-- Expansion of the congruence as a function of the affine parameter. -/
  theta : ℝ → ℝ
  /-- Derivative of the expansion with respect to the affine parameter. -/
  dtheta : ℝ → ℝ
  /-- `dtheta` really is the derivative of `theta` on the affine parameter range. -/
  hasDerivAt : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta t) t
  /-- Raychaudhuri's equation together with the null energy condition (`Ric (k, k) ≥ 0`)
  and vanishing vorticity. -/
  raychaudhuri : ∀ t ∈ Set.Ico (0 : ℝ) L, dtheta t ≤ -(theta t) ^ 2 / 2

/-- A surface is *trapped* (for this congruence) when the initial expansion of the
orthogonal null congruence is negative. -/
def NullCongruence.Trapped {L : ℝ} (C : NullCongruence L) : Prop := C.theta 0 < 0

namespace NullCongruence

variable {L : ℝ} (C : NullCongruence L)

/-- Along a compact subinterval `[0, c]` of the affine range on which the expansion is
negative at `0`, the expansion stays negative: it is antitone by Raychaudhuri. -/
theorem theta_le_of_mem_Icc {c : ℝ} (hc : Set.Icc 0 c ⊆ Set.Ico 0 L) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) c) : C.theta t ≤ C.theta 0 := by
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) c, HasDerivAt C.theta (C.dtheta x) x := fun x hx =>
    C.hasDerivAt x (hc hx)
  have hcont : ContinuousOn C.theta (Set.Icc 0 c) := fun x hx =>
    ((hderiv x hx).continuousAt).continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) c) ⊆ Set.Icc 0 c := interior_subset
  have hdiff : DifferentiableOn ℝ C.theta (interior (Set.Icc (0 : ℝ) c)) := fun x hx =>
    ((hderiv x (hint hx)).differentiableAt).differentiableWithinAt
  have hanti : AntitoneOn C.theta (Set.Icc 0 c) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 c) hcont hdiff ?_
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) c := hint hx
    have hd : deriv C.theta x = C.dtheta x := (hderiv x hx').deriv
    have := C.raychaudhuri x (hc hx')
    nlinarith [sq_nonneg (C.theta x), hd]
  exact hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

end NullCongruence

/-- **Penrose singularity theorem (focusing core).**

If the future-directed null geodesic congruence orthogonal to a trapped surface
satisfies the Raychaudhuri inequality coming from the null energy condition
(`theta' ≤ -theta ^ 2 / 2`) on its affine parameter range `[0, L)`, then that range is
necessarily bounded by `-2 / theta 0`.  Equivalently: the congruence focuses to a
conjugate (focal) point within affine parameter `-2 / theta 0`, and so the geodesics
cannot be extended indefinitely — the spacetime is null geodesically incomplete. -/
theorem penrose_singularity {L : ℝ} (C : NullCongruence L) (htrap : C.Trapped) :
    L ≤ -2 / C.theta 0 := by
  have hθ0 : C.theta 0 < 0 := htrap
  by_contra hL
  push_neg at hL
  set c : ℝ := -2 / C.theta 0 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact div_pos_of_neg_of_neg (by norm_num) hθ0
  have hc : Set.Icc 0 c ⊆ Set.Ico 0 L := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hL⟩
  -- The expansion stays `≤ theta 0 < 0` on `[0, c]`, in particular it never vanishes.
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) c, C.theta t < 0 := fun t ht =>
    lt_of_le_of_lt (C.theta_le_of_mem_Icc hc ht) hθ0
  -- Consider `w t = (theta t)⁻¹ - t / 2`; Raychaudhuri says `w` is monotone.
  set w : ℝ → ℝ := fun t => (C.theta t)⁻¹ - t / 2 with hwdef
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) c,
      HasDerivAt w (-(C.dtheta t) / (C.theta t) ^ 2 - 1 / 2) t := by
    intro t ht
    have h1 : HasDerivAt C.theta (C.dtheta t) t := C.hasDerivAt t (hc ht)
    have h2 : HasDerivAt (fun x => (C.theta x)⁻¹) (-(C.dtheta t) / (C.theta t) ^ 2) t :=
      h1.inv (ne_of_lt (hneg t ht))
    have h3 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    exact h2.sub h3
  have hcont : ContinuousOn w (Set.Icc 0 c) := fun x hx =>
    ((hderiv x hx).continuousAt).continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) c) ⊆ Set.Icc 0 c := interior_subset
  have hdiff : DifferentiableOn ℝ w (interior (Set.Icc (0 : ℝ) c)) := fun x hx =>
    ((hderiv x (hint hx)).differentiableAt).differentiableWithinAt
  have hmono : MonotoneOn w (Set.Icc 0 c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 c) hcont hdiff ?_
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) c := hint hx
    have hd : deriv w x = -(C.dtheta x) / (C.theta x) ^ 2 - 1 / 2 := (hderiv x hx').deriv
    have hray := C.raychaudhuri x (hc hx')
    have hxne : C.theta x < 0 := hneg x hx'
    have hsq : (0 : ℝ) < (C.theta x) ^ 2 := by nlinarith
    rw [hd, sub_nonneg, le_div_iff₀ hsq]
    linarith
  -- Monotonicity from `0` to `c` gives `(theta c)⁻¹ ≥ 0`, contradicting `theta c < 0`.
  have hle : w 0 ≤ w c := hmono (Set.left_mem_Icc.2 hcpos.le) (Set.right_mem_Icc.2 hcpos.le) hcpos.le
  have hc2 : c / 2 = -(C.theta 0)⁻¹ := by
    rw [hcdef]
    field_simp
  have hcneg : C.theta c < 0 := hneg c (Set.right_mem_Icc.2 hcpos.le)
  have hinvneg : (C.theta c)⁻¹ < 0 := inv_neg''.2 hcneg
  simp only [hwdef, sub_zero, zero_div] at hle
  rw [hc2] at hle
  linarith

/-- **Penrose singularity theorem: null geodesic incompleteness.**

There is no *complete* future-directed null geodesic congruence orthogonal to a trapped
surface obeying the null energy condition: if the expansion `theta` of such a congruence
were defined (and satisfied the Raychaudhuri inequality `theta' ≤ -theta ^ 2 / 2`) for
*all* affine parameters `t ≥ 0`, and the surface is trapped (`theta 0 < 0`), we obtain a
contradiction.  Hence the spacetime is null geodesically incomplete. -/
theorem penrose_null_geodesically_incomplete (theta dtheta : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt theta (dtheta t) t)
    (hray : ∀ t ∈ Set.Ici (0 : ℝ), dtheta t ≤ -(theta t) ^ 2 / 2)
    (htrap : theta 0 < 0) : False := by
  set L : ℝ := -2 / theta 0 + 1 with hLdef
  have hsub : Set.Ico (0 : ℝ) L ⊆ Set.Ici (0 : ℝ) := fun x hx => hx.1
  let C : NullCongruence L :=
    { theta := theta
      dtheta := dtheta
      hasDerivAt := fun t ht => hderiv t (hsub ht)
      raychaudhuri := fun t ht => hray t (hsub ht) }
  have h := penrose_singularity C htrap
  simp only [C, hLdef] at h
  linarith

/-!
## A second, more geometric formulation: focal points of the transverse Jacobi field

Instead of the expansion one may follow the transverse *area radius* `rho` of the
congruence (the square root of the cross-sectional area element, i.e. the relevant
Jacobi field along the null geodesics), related to the expansion by `theta = 2 rho' / rho`.
In these variables the Raychaudhuri equation becomes the Jacobi equation

  `rho'' = -(shear ^ 2 + Ric (k, k) / 2) * rho`,

so that the null energy condition says exactly `rho'' ≤ 0` as long as `rho > 0`.  A
*trapped* surface means the congruence is initially contracting, `rho' 0 < 0`, and the
congruence is regular (no focal point yet) exactly while `rho > 0`.
-/

/-- Transverse Jacobi (area-radius) data of the null geodesic congruence orthogonal to a
closed spacelike surface, on the affine parameter range `[0, L)` on which the congruence
is still regular (`rho > 0`, i.e. no focal point has been reached).

The null energy condition enters through the Jacobi equation as the concavity
condition `rho'' ≤ 0`. -/
structure NullJacobi (L : ℝ) where
  /-- Transverse area radius of the congruence. -/
  rho : ℝ → ℝ
  /-- Its first derivative in the affine parameter. -/
  drho : ℝ → ℝ
  /-- Its second derivative in the affine parameter. -/
  ddrho : ℝ → ℝ
  /-- `drho` is the derivative of `rho`. -/
  hasDerivAt_rho : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt rho (drho t) t
  /-- `ddrho` is the derivative of `drho`. -/
  hasDerivAt_drho : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt drho (ddrho t) t
  /-- No focal point has been reached on `[0, L)`. -/
  rho_pos : ∀ t ∈ Set.Ico (0 : ℝ) L, 0 < rho t
  /-- The Jacobi equation together with the null energy condition: `rho'' ≤ 0`. -/
  jacobi_nec : ∀ t ∈ Set.Ico (0 : ℝ) L, ddrho t ≤ 0

/-- The expansion `theta = 2 rho' / rho` of a transverse Jacobi field satisfies the
Raychaudhuri inequality, so it defines a `NullCongruence`. -/
noncomputable def NullJacobi.toNullCongruence {L : ℝ} (J : NullJacobi L) : NullCongruence L where
  theta := fun t => 2 * J.drho t / J.rho t
  dtheta := fun t => (2 * J.ddrho t * J.rho t - 2 * J.drho t * J.drho t) / J.rho t ^ 2
  hasDerivAt := by
    intro t ht
    have h1 : HasDerivAt (fun x => 2 * J.drho x) (2 * J.ddrho t) t :=
      (J.hasDerivAt_drho t ht).const_mul 2
    have h2 : HasDerivAt J.rho (J.drho t) t := J.hasDerivAt_rho t ht
    exact h1.div h2 (ne_of_gt (J.rho_pos t ht))
  raychaudhuri := by
    intro t ht
    have hpos : 0 < J.rho t := J.rho_pos t ht
    have hsq : (0 : ℝ) < J.rho t ^ 2 := by positivity
    have hdd : J.ddrho t ≤ 0 := J.jacobi_nec t ht
    rw [div_le_iff₀ hsq]
    have hexp : -(2 * J.drho t / J.rho t) ^ 2 / 2 * J.rho t ^ 2 = -2 * J.drho t ^ 2 := by
      field_simp
    rw [hexp]
    nlinarith

/-- **Penrose singularity theorem, focal-point form.**

If the null geodesic congruence orthogonal to a trapped surface (`rho' 0 < 0`) obeys the
null energy condition in Jacobi form (`rho'' ≤ 0`), then it stays regular (`rho > 0`) only
for affine parameter less than `-rho 0 / rho' 0`: a focal point of the surface occurs at or
before that affine parameter.  Consequently the congruence — and hence the spacetime —
cannot be null geodesically complete. -/
theorem penrose_focal_point {L : ℝ} (J : NullJacobi L) (hL : 0 < L) (htrap : J.drho 0 < 0) :
    L ≤ -J.rho 0 / J.drho 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) L := ⟨le_rfl, hL⟩
  have hpos : 0 < J.rho 0 := J.rho_pos 0 h0
  have htr : (J.toNullCongruence).Trapped := by
    show 2 * J.drho 0 / J.rho 0 < 0
    exact div_neg_of_neg_of_pos (by linarith) hpos
  have h := penrose_singularity J.toNullCongruence htr
  have hne : J.drho 0 ≠ 0 := ne_of_lt htrap
  have hrw : -2 / (2 * J.drho 0 / J.rho 0) = -J.rho 0 / J.drho 0 := by
    field_simp
  calc L ≤ -2 / ((J.toNullCongruence).theta 0) := h
    _ = -J.rho 0 / J.drho 0 := hrw

/-- Concavity bound: if `rho'' ≤ 0` on `[0, ∞)` then `rho` lies below its tangent line at
`0`, `rho t ≤ rho 0 + rho' 0 * t`.  This is the integrated form of the null energy
condition in Jacobi variables. -/
theorem rho_le_tangent (rho drho ddrho : ℝ → ℝ)
    (hrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt rho (drho t) t)
    (hdrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt drho (ddrho t) t)
    (hnec : ∀ t ∈ Set.Ici (0 : ℝ), ddrho t ≤ 0) :
    ∀ t ∈ Set.Ici (0 : ℝ), rho t ≤ rho 0 + drho 0 * t := by
  -- First: `drho` is antitone on `[0, ∞)`.
  have hdrho_anti : AntitoneOn drho (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx => ((hdrho x hx).continuousAt).continuousWithinAt)
      (fun x hx => ((hdrho x (interior_subset hx)).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hdrho x hx').deriv]
    exact hnec x hx'
  -- Then `g t = rho t - (rho 0 + drho 0 * t)` has nonpositive derivative, so is antitone.
  set g : ℝ → ℝ := fun t => rho t - (rho 0 + drho 0 * t) with hgdef
  have hgderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt g (drho t - drho 0) t := by
    intro t ht
    have h1 : HasDerivAt rho (drho t) t := hrho t ht
    have h2 : HasDerivAt (fun x : ℝ => rho 0 + drho 0 * x) (drho 0) t := by
      simpa using ((hasDerivAt_id t).const_mul (drho 0)).const_add (rho 0)
    exact h1.sub h2
  have hg_anti : AntitoneOn g (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx => ((hgderiv x hx).continuousAt).continuousWithinAt)
      (fun x hx => ((hgderiv x (interior_subset hx)).differentiableAt).differentiableWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hgderiv x hx').deriv, sub_nonpos]
    exact hdrho_anti (Set.self_mem_Ici) hx' hx'
  intro t ht
  have := hg_anti (Set.self_mem_Ici) ht ht
  simp only [hgdef, mul_zero, add_zero, sub_self] at this
  linarith

/-- **Penrose singularity theorem: incompleteness, focal-point form.**

A trapped null congruence (`rho' 0 < 0`, `rho 0 > 0`) obeying the null energy condition in
Jacobi form (`rho'' ≤ 0`) cannot remain regular for all affine parameters: the transverse
area radius vanishes (a focal point of the trapped surface forms) at some affine parameter
`t ≤ -rho 0 / rho' 0`. -/
theorem penrose_focal_point_incomplete (rho drho ddrho : ℝ → ℝ)
    (hrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt rho (drho t) t)
    (hdrho : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt drho (ddrho t) t)
    (hnec : ∀ t ∈ Set.Ici (0 : ℝ), ddrho t ≤ 0)
    (htrap : drho 0 < 0) (hrho0 : 0 < rho 0) :
    ∃ t ∈ Set.Ioc (0 : ℝ) (-rho 0 / drho 0), rho t ≤ 0 := by
  have hcpos : 0 < -rho 0 / drho 0 := div_pos_of_neg_of_neg (by linarith) htrap
  refine ⟨-rho 0 / drho 0, ⟨hcpos, le_rfl⟩, ?_⟩
  have h := rho_le_tangent rho drho ddrho hrho hdrho hnec (-rho 0 / drho 0) hcpos.le
  have hne : drho 0 ≠ 0 := ne_of_lt htrap
  have : rho 0 + drho 0 * (-rho 0 / drho 0) = 0 := by field_simp; ring
  linarith

/-!
## Non-vacuity and sharpness

The hypotheses are satisfiable and the bound is attained: the focusing of the past light
cone of a point in flat space, `rho t = 1 - t` (`rho'' = 0`, i.e. the null energy condition
saturated), is a trapped congruence regular exactly on `[0, 1)`, with
`-rho 0 / rho' 0 = 1`.
-/

/-- The flat-space example `rho t = 1 - t`, a trapped null congruence obeying the null
energy condition and regular exactly on the affine range `[0, 1)`. -/
def flatJacobi : NullJacobi 1 where
  rho := fun t => 1 - t
  drho := fun _ => -1
  ddrho := fun _ => 0
  hasDerivAt_rho := fun t _ => by simpa using (hasDerivAt_id t).const_sub 1
  hasDerivAt_drho := fun t _ => hasDerivAt_const t (-1)
  rho_pos := fun t ht => by show (0:ℝ) < 1 - t; linarith [ht.2]
  jacobi_nec := fun _ _ => le_rfl

/-- The affine bound of `Frontier.penrose_focal_point` is sharp: for `flatJacobi` it equals
the actual affine length `1` of the regular range. -/
theorem penrose_focal_point_sharp :
    -flatJacobi.rho 0 / flatJacobi.drho 0 = 1 := by
  show -(1 - (0 : ℝ)) / (-1) = 1
  norm_num

end Frontier

#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_null_geodesically_incomplete
#print axioms Frontier.penrose_focal_point
#print axioms Frontier.penrose_focal_point_incomplete

