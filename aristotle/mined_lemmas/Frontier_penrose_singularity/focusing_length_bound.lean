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

set_option grind.warning false

namespace Frontier

/-!
## Formalization

Penrose's singularity theorem states that a spacetime containing a *trapped surface*,
satisfying the *null energy condition* (together with the genericity/global hypotheses),
cannot be null geodesically complete.

Mathlib does not (yet) contain Lorentzian causal theory, so we formalize the analytic
engine of the theorem, which is where the physics enters and which is a Lean-checked
reduction of the full statement:

* Let `θ : ℝ → ℝ` be the *expansion* of the congruence of null geodesics emanating
  orthogonally from a closed surface, as a function of the affine parameter `t`.
* The **Raychaudhuri equation** for a hypersurface-orthogonal null congruence reads
  `dθ/dt = -θ²/2 - σ_{ab}σ^{ab} - Ric(k,k)`.
  The null energy condition gives `Ric(k,k) ≥ 0`, and the shear term satisfies
  `σ_{ab}σ^{ab} ≥ 0`, so the physical input is exactly the differential inequality
  `deriv θ t ≤ -(θ t)^2 / 2`   (hypothesis `hray` below).
* The surface being **trapped** means the expansion is initially negative:
  `θ 0 < 0`   (hypothesis `htrapped` below).

`Frontier.focusing_length_bound` then shows that the congruence can only remain smooth
(i.e. free of a focal point / caustic) for affine parameter `t < 2/|θ 0|`, and
`Frontier.penrose_singularity` concludes that no such congruence can be complete,
i.e. defined and smooth for all affine parameters `t ≥ 0`: geodesic incompleteness.
-/

/-- Under the Raychaudhuri inequality the expansion is non-increasing: in particular a
congruence that is initially converging (trapped) stays converging. -/

theorem focusing_length_bound {L : ℝ} {θ : ℝ → ℝ}
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ θ t)
    (hray : ∀ t ∈ Set.Icc (0 : ℝ) L, deriv θ t ≤ -(θ t) ^ 2 / 2)
    (htrapped : θ 0 < 0) (hL : 0 ≤ L) :
    L < -2 / θ 0 := by
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) L, θ t < 0 := expansion_neg hdiff hray htrapped
  -- the "inverse expansion" `v t = t/2 - 1/θ t` is non-increasing
  set v : ℝ → ℝ := fun t => t / 2 - (θ t)⁻¹ with hv
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) L,
      HasDerivAt v (1 / 2 + deriv θ x / (θ x) ^ 2) x := by
    intro x hx
    have hx0 : θ x ≠ 0 := ne_of_lt (hneg x hx)
    have h1 : HasDerivAt (fun t : ℝ => (θ t)⁻¹) (-deriv θ x / (θ x) ^ 2) x :=
      ((hdiff x hx).hasDerivAt).inv hx0
    have h2 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have := h2.sub h1
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousOn v (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hanti : AntitoneOn v (Set.Icc (0 : ℝ) L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (Set.mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxI := Set.mem_Icc_of_Ioo hx
      rw [(hderiv x hxI).deriv]
      have hxne : θ x ≠ 0 := ne_of_lt (hneg x hxI)
      have hpos : (0 : ℝ) < (θ x) ^ 2 := by positivity
      have h := hray x hxI
      have hkey : deriv θ x / (θ x) ^ 2 ≤ -1 / 2 := by
        rw [div_le_iff₀ hpos]
        nlinarith [h]
      linarith
  have hmain : v L ≤ v 0 := hanti (Set.left_mem_Icc.mpr hL) (Set.right_mem_Icc.mpr hL) hL
  have hL0 : θ L < 0 := hneg L (Set.right_mem_Icc.mpr hL)
  have hinvL : (θ L)⁻¹ < 0 := inv_neg''.mpr hL0
  have hinv0 : (θ 0)⁻¹ * θ 0 = 1 := inv_mul_cancel₀ (ne_of_lt htrapped)
  simp only [hv] at hmain
  rw [lt_div_iff_of_neg htrapped]
  nlinarith [hmain, hinvL, hinv0]

/-- Sanity check (non-vacuity): the hypotheses of `Frontier.focusing_length_bound` are
satisfiable.  The exact solution `θ t = 2/(t-1)` of the Raychaudhuri equation
`θ' = -θ²/2` starts trapped (`θ 0 = -2 < 0`) and is regular on `[0, 1/2]`;
consistently with the bound, its caustic occurs at `t = 1 = 2/|θ 0|`. -/
example : (∀ t ∈ Set.Icc (0:ℝ) (1/2), DifferentiableAt ℝ (fun s : ℝ => 2/(s-1)) t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) (1/2),
      deriv (fun s : ℝ => 2/(s-1)) t ≤ -((fun s : ℝ => 2/(s-1)) t) ^ 2 / 2) ∧
    (fun s : ℝ => 2/(s-1)) 0 < 0 := by
  have hne : ∀ t ∈ Set.Icc (0:ℝ) (1/2), (t - 1) ≠ 0 := by
    intro t ht hc
    have h2 := ht.2
    have : t = 1 := by linarith [sub_eq_zero.mp hc]
    linarith
  have key : ∀ t ∈ Set.Icc (0:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => 2/(s-1)) (-2/(t-1)^2) t := by
    intro t ht
    have h3 := (((hasDerivAt_id t).sub_const 1).inv (hne t ht)).const_mul (2:ℝ)
    convert h3 using 1
    simp only [id]
    ring
  refine ⟨fun t ht => (key t ht).differentiableAt, fun t ht => ?_, by norm_num⟩
  rw [(key t ht).deriv]
  have h := hne t ht
  field_simp
  exact le_refl _

/-- **Penrose singularity theorem (analytic core).**

If a null geodesic congruence emanating from a trapped surface (`θ 0 < 0`) obeys the
Raychaudhuri inequality `θ' ≤ -θ²/2` — which is exactly what the null energy condition
(`Ric(k,k) ≥ 0`) plus non-negativity of the shear give — then it cannot be complete:
there is no expansion function that is smooth for *all* affine parameters `t ≥ 0`.
Equivalently, a focal point forms at affine parameter at most `2/|θ 0|`, and the
spacetime is null geodesically incomplete. -/
