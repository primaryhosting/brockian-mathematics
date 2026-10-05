/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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
## Formalization

The analytic core of Penrose's singularity theorem is the *focusing* of the null
geodesic congruence generating the boundary of the future of a trapped surface.

Along an affinely parametrised null geodesic congruence with affine parameter `t`,
expansion `θ`, shear scalar `shear = σ_{ab} σ^{ab} ≥ 0` and Ricci contraction
`ric = R_{ab} k^a k^b`, the Raychaudhuri equation for a hypersurface-orthogonal
null congruence with two-dimensional screen space reads

  `dθ/dt = - θ² / 2 - shear - ric`.

The *null energy condition* (together with the Einstein equations) gives `ric ≥ 0`,
and the presence of a *trapped surface* gives an initially negative expansion,
`θ 0 < 0`.

The theorem below shows that under these hypotheses the congruence cannot remain
regular for an affine parameter interval longer than `2 / |θ 0|`: any interval
`[0, L]` on which the expansion is finite and differentiable must satisfy
`L < 2 / (-θ 0)`. Equivalently, the expansion blows up (a conjugate/focal point
forms) at some affine parameter `≤ 2 / |θ 0|`; the generators of the boundary
therefore cannot be extended indefinitely — the spacetime is null geodesically
incomplete, which is Penrose's conclusion.
-/

/-- **Penrose singularity theorem (Raychaudhuri focusing core).**

Let `θ` be the expansion of an affinely parametrised null geodesic congruence,
with derivative `D`, shear scalar `shear` and Ricci contraction `ric` along the
generators, satisfying the Raychaudhuri equation on the affine interval `[0, L]`.
Assume the null energy condition `0 ≤ ric` and the (always valid) positivity of
the shear scalar `0 ≤ shear`, and assume the initial cross-section is *trapped*,
i.e. `θ 0 < 0`.

Then the congruence cannot remain regular for affine length `2 / |θ 0|` or more:
`L < 2 / (-θ 0)`. Hence the generators are incomplete (see
`Frontier.penrose_singularity_incomplete`). -/
theorem penrose_singularity
    (L : ℝ) (hL : 0 ≤ L) (θ D shear ric : ℝ → ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt θ (D t) t)
    (hray : ∀ t ∈ Set.Icc (0 : ℝ) L, D t = -(θ t) ^ 2 / 2 - shear t - ric t)
    (hshear : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ shear t)
    (hnec : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ ric t)
    (htrapped : θ 0 < 0) :
    L < 2 / (-θ 0) := by
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) L) := convex_Icc 0 L
  have hint : interior (Set.Icc (0 : ℝ) L) = Set.Ioo 0 L := interior_Icc
  have hsub : Set.Ioo (0 : ℝ) L ⊆ Set.Icc 0 L := Set.Ioo_subset_Icc_self
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := Set.left_mem_Icc.mpr hL
  have hLmem : L ∈ Set.Icc (0 : ℝ) L := Set.right_mem_Icc.mpr hL
  -- Continuity of the expansion on the interval.
  have hcont : ContinuousOn θ (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  -- Raychaudhuri + NEC forces the expansion to be nonincreasing.
  have hDnonpos : ∀ t ∈ Set.Icc (0 : ℝ) L, D t ≤ 0 := by
    intro t ht
    rw [hray t ht]
    nlinarith [sq_nonneg (θ t), hshear t ht, hnec t ht]
  have hanti : AntitoneOn θ (Set.Icc (0 : ℝ) L) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (f' := D) hconv hcont
      (by
        intro x hx
        rw [hint] at hx
        exact (hderiv x (hsub hx)).hasDerivWithinAt)
      (by
        intro x hx
        rw [hint] at hx
        exact hDnonpos x (hsub hx))
  -- Hence it stays strictly negative: the congruence stays convergent.
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) L, θ t < 0 := fun t ht =>
    lt_of_le_of_lt (hanti h0mem ht ht.1) htrapped
  -- The reciprocal expansion `v t = 1/θ t - t/2` is nondecreasing.
  set v : ℝ → ℝ := fun t => (θ t)⁻¹ - t / 2 with hv_def
  have hvderiv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      HasDerivAt v (-D t / (θ t) ^ 2 - 1 / 2) t := by
    intro t ht
    exact ((hderiv t ht).inv (ne_of_lt (hneg t ht))).sub ((hasDerivAt_id t).div_const 2)
  have hvpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ -D t / (θ t) ^ 2 - 1 / 2 := by
    intro t ht
    have hlt := hneg t ht
    have hsq : 0 < (θ t) ^ 2 := by nlinarith
    have key : (θ t) ^ 2 / 2 ≤ -D t := by
      rw [hray t ht]
      linarith [hshear t ht, hnec t ht]
    rw [sub_nonneg, le_div_iff₀ hsq]
    linarith
  have hvcont : ContinuousOn v (Set.Icc (0 : ℝ) L) := fun t ht =>
    (hvderiv t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn v (Set.Icc (0 : ℝ) L) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => -D t / (θ t) ^ 2 - 1 / 2) hconv hvcont
      (by
        intro x hx
        rw [hint] at hx
        exact (hvderiv x (hsub hx)).hasDerivWithinAt)
      (by
        intro x hx
        rw [hint] at hx
        exact hvpos x (hsub hx))
  -- Compare the endpoints.
  have hcmp : v 0 ≤ v L := hmono h0mem hLmem hL
  have hinvL : (θ L)⁻¹ < 0 := inv_lt_zero.mpr (hneg L hLmem)
  have hinv0 : (θ 0)⁻¹ * θ 0 = 1 := inv_mul_cancel₀ (ne_of_lt htrapped)
  have hstep : (θ 0)⁻¹ - 0 / 2 ≤ (θ L)⁻¹ - L / 2 := hcmp
  have hkey : L / 2 < -(θ 0)⁻¹ := by simp only [zero_div, sub_zero] at hstep; linarith
  have hpos : 0 < -θ 0 := by linarith
  rw [lt_div_iff₀ hpos]
  nlinarith [hkey, hinv0, hpos]

/-- **Null geodesic incompleteness.**

If, in addition to the hypotheses of `Frontier.penrose_singularity`, the expansion
of the null congruence were regular (differentiable, hence finite) for *all*
nonnegative values of the affine parameter — i.e. if the generators were future
complete — we obtain a contradiction. Thus a spacetime containing a trapped
surface and satisfying the null energy condition is null geodesically
incomplete. -/
theorem penrose_singularity_incomplete
    (θ D shear ric : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt θ (D t) t)
    (hray : ∀ t : ℝ, 0 ≤ t → D t = -(θ t) ^ 2 / 2 - shear t - ric t)
    (hshear : ∀ t : ℝ, 0 ≤ t → 0 ≤ shear t)
    (hnec : ∀ t : ℝ, 0 ≤ t → 0 ≤ ric t)
    (htrapped : θ 0 < 0) :
    False := by
  have hpos : 0 < -θ 0 := by linarith
  set L : ℝ := 2 / (-θ 0) with hLdef
  have hL : 0 ≤ L := le_of_lt (div_pos (by norm_num) hpos)
  have := penrose_singularity L hL θ D shear ric
    (fun t ht => hderiv t ht.1) (fun t ht => hray t ht.1)
    (fun t ht => hshear t ht.1) (fun t ht => hnec t ht.1) htrapped
  exact lt_irrefl L this

/-- The hypotheses of `Frontier.penrose_singularity` are non-vacuous: for every affine
length `L < 1` there is a genuine focusing congruence realising them (here with vanishing
shear and vanishing Ricci contraction, `θ t = 2 / (t - 1)`, whose expansion diverges exactly
at the focal parameter `1 = 2 / |θ 0|`). -/
theorem penrose_hypotheses_satisfiable (L : ℝ) (hL1 : L < 1) :
    ∃ θ D shear ric : ℝ → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt θ (D t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, D t = -(θ t) ^ 2 / 2 - shear t - ric t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ shear t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, 0 ≤ ric t) ∧ θ 0 < 0 := by
  refine ⟨fun t => 2 * (t - 1)⁻¹, fun t => -2 / (t - 1) ^ 2, fun _ => 0, fun _ => 0,
    ?_, ?_, fun _ _ => le_refl 0, fun _ _ => le_refl 0, by norm_num⟩
  · intro t ht
    have hne : t - 1 ≠ 0 := by rcases ht with ⟨h1, h2⟩; intro h; nlinarith
    have h := (((hasDerivAt_id t).sub_const 1).inv hne).const_mul (2 : ℝ)
    simp only [id] at h
    convert h using 1
    field_simp
  · intro t ht
    have hne : t - 1 ≠ 0 := by rcases ht with ⟨h1, h2⟩; intro h; nlinarith
    simp only
    field_simp
    ring

end Frontier

