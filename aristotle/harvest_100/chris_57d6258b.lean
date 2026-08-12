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

/-!
## Setting

The analytic core of Penrose's singularity theorem is the focusing of a null geodesic
congruence.  Along a null generator of the boundary of the future of a closed trapped
surface, with affine parameter `t`, the expansion `θ` of the congruence satisfies the
Raychaudhuri equation

  `dθ/dt = -θ² / 2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`,

where `σ` is the shear and `k` is the null tangent.  The null energy condition gives
`R_{ab} k^a k^b ≥ 0`, and the shear term is nonnegative, so the *Raychaudhuri inequality*

  `dθ/dt ≤ -θ² / 2`

holds.  That the surface is *trapped* means precisely that the initial expansion of the
outgoing null congruence is negative: `θ 0 < 0`.

The structure `NullGeneratorData L` below packages exactly this data on an affine
interval `[0, L]`: the expansion along a null generator that is defined (and
differentiable, with finite expansion) for affine parameter in `[0, L]`, satisfying the
Raychaudhuri inequality, and emanating from a trapped surface.

The theorem `Frontier.penrose_singularity` states that such a generator can only exist for
affine length `L < 2 / |θ 0|`: the null geodesic congruence focuses to a conjugate point in
finite affine parameter, so the generator cannot be extended, i.e. the spacetime is null
geodesically incomplete (`Frontier.penrose_null_geodesic_incomplete`).
-/

/-- Data of a null geodesic generator, parametrized by affine parameter in `[0, L]`,
issuing orthogonally from a closed trapped surface, in a spacetime satisfying the null
energy condition.

* `expansion` is the expansion scalar `θ` of the null congruence;
* `expansionDeriv` is its derivative with respect to the affine parameter;
* `raychaudhuri` is the Raychaudhuri inequality `θ' ≤ -θ²/2`, which follows from the
  Raychaudhuri equation together with the null energy condition and the nonnegativity of
  the shear term;
* `trapped` says that the surface is trapped: the initial expansion is negative. -/
structure NullGeneratorData (L : ℝ) where
  /-- The expansion scalar `θ` of the null congruence along the generator. -/
  expansion : ℝ → ℝ
  /-- The derivative of the expansion with respect to the affine parameter. -/
  expansionDeriv : ℝ → ℝ
  /-- The expansion is differentiable in the affine parameter on `[0, L]`
  (in particular it stays finite there: no conjugate point occurs on `[0, L]`). -/
  hasDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt expansion (expansionDeriv t) t
  /-- Raychaudhuri inequality, a consequence of the null energy condition. -/
  raychaudhuri : ∀ t ∈ Set.Icc (0 : ℝ) L, expansionDeriv t ≤ -(expansion t) ^ 2 / 2
  /-- Trapped surface condition: the initial expansion is negative. -/
  trapped : expansion 0 < 0

namespace NullGeneratorData

variable {L : ℝ} (C : NullGeneratorData L)

/-- The expansion is nonincreasing along the generator. -/
theorem antitoneOn_expansion : AntitoneOn C.expansion (Set.Icc 0 L) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 L) ?_ ?_ ?_
  · exact fun t ht => (C.hasDeriv t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact ((C.hasDeriv t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) L := Set.mem_Icc_of_Ioo ht
    rw [(C.hasDeriv t ht').deriv]
    have := C.raychaudhuri t ht'
    nlinarith [sq_nonneg (C.expansion t)]

/-- The expansion stays strictly negative on the whole interval. -/
theorem expansion_neg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) : C.expansion t < 0 :=
  lt_of_le_of_lt (C.antitoneOn_expansion ⟨le_refl 0, ht.1.trans ht.2⟩ ht ht.1) C.trapped

/-- The auxiliary function `t ↦ 1 / θ t - t / 2`, which is nondecreasing by the
Raychaudhuri inequality. -/
noncomputable def aux : ℝ → ℝ := fun t => 1 / C.expansion t - t / 2

theorem hasDerivAt_aux {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L) :
    HasDerivAt C.aux (-C.expansionDeriv t / (C.expansion t) ^ 2 - 1 / 2) t := by
  have hne : C.expansion t ≠ 0 := ne_of_lt (C.expansion_neg ht)
  have h1 : HasDerivAt (fun s => 1 / C.expansion s)
      (-C.expansionDeriv t / (C.expansion t) ^ 2) t := by
    simpa [one_div] using ((C.hasDeriv t ht).inv hne)
  have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  unfold NullGeneratorData.aux
  exact h1.sub h2

theorem monotoneOn_aux : MonotoneOn C.aux (Set.Icc 0 L) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 L) ?_ ?_ ?_
  · exact fun t ht => (C.hasDerivAt_aux ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact ((C.hasDerivAt_aux (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) L := Set.mem_Icc_of_Ioo ht
    rw [(C.hasDerivAt_aux ht').deriv]
    have hneg : C.expansion t < 0 := C.expansion_neg ht'
    have hsq : 0 < (C.expansion t) ^ 2 := by nlinarith
    have hR : C.expansionDeriv t ≤ -(C.expansion t) ^ 2 / 2 := C.raychaudhuri t ht'
    rw [sub_nonneg, le_div_iff₀ hsq]
    linarith

end NullGeneratorData

/-- **Penrose singularity theorem (focusing core).**

In a spacetime satisfying the null energy condition, a null geodesic generator issuing
from a closed trapped surface (so that the Raychaudhuri inequality `θ' ≤ -θ²/2` holds and
the initial expansion `θ 0` is negative) cannot remain regular for affine parameter
beyond `2 / |θ 0|`: any interval `[0, L]` on which the congruence is defined with finite
expansion satisfies `L < 2 / |θ 0|`.

Thus the generator reaches a conjugate (focal) point within affine parameter `2 / |θ 0|`,
which is the analytic heart of Penrose's theorem: together with compactness of the trapped
surface and the global hyperbolicity/non-compact Cauchy surface hypothesis, it forces null
geodesic incompleteness. -/
theorem penrose_singularity {L : ℝ} (hL : 0 ≤ L) (C : NullGeneratorData L) :
    L < 2 / |C.expansion 0| := by
  have h0 : C.expansion 0 < 0 := C.trapped
  have hL' : C.expansion L < 0 := C.expansion_neg ⟨hL, le_refl L⟩
  have hmono : C.aux 0 ≤ C.aux L :=
    C.monotoneOn_aux ⟨le_refl 0, hL⟩ ⟨hL, le_refl L⟩ hL
  simp only [NullGeneratorData.aux, sub_zero, zero_div] at hmono
  have h1 : 1 / C.expansion L < 0 := by
    exact div_neg_of_pos_of_neg one_pos hL'
  have hid : C.expansion 0 * (1 / C.expansion 0) = 1 := by
    rw [mul_one_div, div_self (ne_of_lt h0)]
  rw [abs_of_neg h0, lt_div_iff₀ (by linarith : (0:ℝ) < -C.expansion 0)]
  nlinarith [hmono, h1, hid, h0]

/-- **Null geodesic incompleteness.**

There is no null generator, emanating from a trapped surface in a spacetime obeying the
null energy condition, that stays regular for *all* affine parameters `t ≥ 0`: the
congruence focuses in finite affine parameter.  Formally, no expansion function `θ` on
`[0, ∞)` can simultaneously satisfy the Raychaudhuri inequality and start with negative
expansion. -/
theorem penrose_null_geodesic_incomplete
    (θ θ' : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt θ (θ' t) t)
    (hray : ∀ t : ℝ, 0 ≤ t → θ' t ≤ -(θ t) ^ 2 / 2)
    (htrapped : θ 0 < 0) : False := by
  set L : ℝ := 2 / |θ 0| + 1 with hLdef
  have habs : 0 < |θ 0| := abs_pos.2 (ne_of_lt htrapped)
  have hLpos : 0 < L := by
    have : 0 < 2 / |θ 0| := by positivity
    linarith [this]
  let C : NullGeneratorData L :=
    { expansion := θ
      expansionDeriv := θ'
      hasDeriv := fun t ht => hderiv t ht.1
      raychaudhuri := fun t ht => hray t ht.1
      trapped := htrapped }
  have := penrose_singularity (le_of_lt hLpos) C
  simp only [C] at this
  rw [hLdef] at this
  linarith

/-!
## Non-vacuity

The hypotheses are consistent: the exact focusing solution `θ t = 2 / (t - 1)` of the
Raychaudhuri equation, on the affine interval `[0, 1/2]`, is a genuine example, and it
blows up exactly at the affine parameter `2 / |θ 0| = 1` predicted by
`Frontier.penrose_singularity`. -/
noncomputable def modelGenerator : NullGeneratorData (1 / 2) where
  expansion := fun t => 2 / (t - 1)
  expansionDeriv := fun t => -2 / (t - 1) ^ 2
  hasDeriv := by
    intro t ht
    have hne : t - 1 ≠ 0 := by
      have h2 := ht.2
      intro h
      rw [sub_eq_zero] at h
      rw [h] at h2
      norm_num at h2
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => (s - 1)⁻¹) (-1 / (t - 1) ^ 2) t := by
      simpa using h1.inv hne
    have h3 := h2.const_mul (2 : ℝ)
    have hfun : (fun s : ℝ => 2 * (s - 1)⁻¹) = fun s : ℝ => 2 / (s - 1) := by
      funext s; rw [div_eq_mul_inv]
    rw [hfun] at h3
    convert h3 using 1
    ring
  raychaudhuri := by
    intro t ht
    have hne : t - 1 ≠ 0 := by
      have h2 := ht.2
      intro h
      rw [sub_eq_zero] at h
      rw [h] at h2
      norm_num at h2
    rw [div_pow]
    field_simp
    exact le_rfl
  trapped := by norm_num

end Frontier

#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_null_geodesic_incomplete

