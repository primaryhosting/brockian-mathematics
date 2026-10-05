import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

Penrose's singularity theorem says that a spacetime containing a trapped surface, satisfying
the null energy condition (plus global hyperbolicity with a non-compact Cauchy surface), is
null geodesically incomplete.  The analytic heart of the theorem is the *focusing* argument:
along the future-directed null geodesic congruence orthogonal to the trapped surface, the
expansion scalar `θ` obeys the Raychaudhuri equation

  `θ' = -θ² / 2 - σ_{ab} σ^{ab} - R_{ab} k^a k^b`,

so that the null energy condition `R_{ab} k^a k^b ≥ 0` gives the differential inequality

  `θ' ≤ -θ² / 2`.

A trapped surface is exactly the condition `θ 0 < 0` for both orthogonal null congruences.
The content proved below is the resulting focusing bound: the affine parameter of such a
congruence cannot reach `2 / |θ 0|`, i.e. a conjugate point (caustic) forms within affine
length `2 / |θ 0|` and the congruence cannot be affinely complete.  This is the base case /
Lean-checked reduction of the singularity theorem: the global step (from a caustic to the
compactness of `∂ J⁺(S)` and the contradiction with non-compactness of a Cauchy surface) is
pure causal topology and is not formalized here.
-/

namespace Frontier

open Set

/-- **Focusing bound (Raychaudhuri + null energy condition).**

If the expansion `θ` of a null geodesic congruence is defined on the affine interval `[0, L]`
with derivative `θ'` there, satisfies the Raychaudhuri–NEC inequality `θ' ≤ -θ²/2`, and starts
out converging, `θ 0 < 0` (the trapped surface condition), then the affine length satisfies
`L < 2 / |θ 0|`: the congruence focuses to a caustic in finite affine parameter. -/
theorem focusing_bound {θ θ' : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hderiv : ∀ s ∈ Icc (0 : ℝ) L, HasDerivAt θ (θ' s) s)
    (hnec : ∀ s ∈ Icc (0 : ℝ) L, θ' s ≤ -(θ s) ^ 2 / 2)
    (htrapped : θ 0 < 0) :
    L < 2 / (-θ 0) := by
  have hconv : Convex ℝ (Icc (0 : ℝ) L) := convex_Icc _ _
  have hint : interior (Icc (0 : ℝ) L) ⊆ Icc (0 : ℝ) L := interior_subset
  have hcont : ContinuousOn θ (Icc (0 : ℝ) L) := fun s hs =>
    ((hderiv s hs).continuousAt).continuousWithinAt
  -- `θ` is nonincreasing on `[0, L]`, hence stays negative.
  have hanti : AntitoneOn θ (Icc (0 : ℝ) L) := by
    refine antitoneOn_of_deriv_nonpos hconv hcont (fun s hs => ?_) (fun s hs => ?_)
    · exact ((hderiv s (hint hs)).differentiableAt).differentiableWithinAt
    · rw [(hderiv s (hint hs)).deriv]
      have := hnec s (hint hs)
      nlinarith [sq_nonneg (θ s)]
  have hneg : ∀ s ∈ Icc (0 : ℝ) L, θ s ≤ θ 0 := fun s hs =>
    hanti (left_mem_Icc.2 hL) hs hs.1
  have hlt : ∀ s ∈ Icc (0 : ℝ) L, θ s < 0 := fun s hs => lt_of_le_of_lt (hneg s hs) htrapped
  -- The function `s ↦ 1/θ s - s/2` is nondecreasing on `[0, L]`.
  set g : ℝ → ℝ := fun s => (θ s)⁻¹ - s / 2 with hg
  have hgderiv : ∀ s ∈ Icc (0 : ℝ) L,
      HasDerivAt g (-(θ' s) / (θ s) ^ 2 - 1 / 2) s := by
    intro s hs
    have h1 : HasDerivAt (fun x => (θ x)⁻¹) (-(θ' s) / (θ s) ^ 2) s :=
      (hderiv s hs).inv (ne_of_lt (hlt s hs))
    have h2 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact h1.sub h2
  have hmono : MonotoneOn g (Icc (0 : ℝ) L) := by
    refine monotoneOn_of_deriv_nonneg hconv (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
    · exact ((hgderiv s hs).continuousAt).continuousWithinAt
    · exact ((hgderiv s (hint hs)).differentiableAt).differentiableWithinAt
    · rw [(hgderiv s (hint hs)).deriv]
      have hs' := hint hs
      have hne : θ s < 0 := hlt s hs'
      have hsq : 0 < (θ s) ^ 2 := by nlinarith
      have := hnec s hs'
      rw [sub_nonneg, le_div_iff₀ hsq]
      nlinarith
  have hkey : g 0 ≤ g L := hmono (left_mem_Icc.2 hL) (right_mem_Icc.2 hL) hL
  have hL0 : θ L < 0 := hlt L (right_mem_Icc.2 hL)
  have hinvL : (θ L)⁻¹ < 0 := inv_neg''.2 hL0
  have hinv0 : (θ 0)⁻¹ < 0 := inv_neg''.2 htrapped
  simp only [hg] at hkey
  have hpos : 0 < -θ 0 := by linarith
  rw [lt_div_iff₀ hpos]
  have hne0 : θ 0 ≠ 0 := ne_of_lt htrapped
  have h0 : (θ 0)⁻¹ * (-θ 0) = -1 := by
    field_simp
  nlinarith [hkey, hinvL, hpos, h0]

/-- **Penrose singularity theorem (focusing form).**

A spacetime containing a trapped surface (`θ 0 < 0` for the orthogonal null congruence) and
satisfying the null energy condition — which through the Raychaudhuri equation gives
`θ' ≤ -θ²/2` — has no affinely complete future null geodesic congruence orthogonal to the
surface: the assumption that the expansion is defined for all affine parameters `s ≥ 0` is
contradictory.  Hence the spacetime is null geodesically incomplete. -/
theorem penrose_singularity {θ θ' : ℝ → ℝ}
    (hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt θ (θ' s) s)
    (hnec : ∀ s ∈ Ici (0 : ℝ), θ' s ≤ -(θ s) ^ 2 / 2)
    (htrapped : θ 0 < 0) :
    False := by
  set L : ℝ := 2 / (-θ 0) with hLdef
  have hpos : 0 < -θ 0 := by linarith
  have hL : 0 ≤ L := by positivity
  have hsub : Icc (0 : ℝ) L ⊆ Ici (0 : ℝ) := Icc_subset_Ici_self
  have := focusing_bound hL (fun s hs => hderiv s (hsub hs)) (fun s hs => hnec s (hsub hs))
    htrapped
  exact absurd this (lt_irrefl L)

/-- **The hypotheses are not vacuous, and the bound is sharp.**

For every affine length `L < 1` there is a congruence expansion `θ s = 2 / (s - 1)` defined on
`[0, L]` that saturates the Raychaudhuri–NEC inequality and starts trapped with `θ 0 = -2`,
so that the focusing bound `L < 2 / |θ 0| = 1` of `Frontier.focusing_bound` cannot be
improved. -/
theorem focusing_bound_sharp {L : ℝ} (hL1 : L < 1) :
    ∃ θ θ' : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) L, HasDerivAt θ (θ' s) s) ∧
      (∀ s ∈ Icc (0 : ℝ) L, θ' s ≤ -(θ s) ^ 2 / 2) ∧ θ 0 < 0 ∧ 2 / (-θ 0) = 1 := by
  refine ⟨fun s => 2 / (s - 1), fun s => -2 / (s - 1) ^ 2, ?_, ?_, by norm_num, by norm_num⟩
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      have := hs.2
      intro h
      linarith [sub_eq_zero.1 h]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 : HasDerivAt (fun x : ℝ => (x - 1)⁻¹) (-1 / (s - 1) ^ 2) s := h1.inv hne
    have h3 := h2.const_mul (2 : ℝ)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h3
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      have := hs.2
      intro h
      linarith [sub_eq_zero.1 h]
    have heq : -2 / (s - 1) ^ 2 = -(2 / (s - 1)) ^ 2 / 2 := by
      field_simp
    exact heq.le

end Frontier

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

