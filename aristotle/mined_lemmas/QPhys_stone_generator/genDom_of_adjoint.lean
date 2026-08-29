/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Mathlib (as of this version) contains no form of Stone's theorem on one-parameter unitary
groups, so the generator, its domain, and the proof of self-adjointness are developed here
from scratch.  The Mathlib inputs used are the fundamental theorem of calculus for
Banach-space valued interval integrals (`intervalIntegral.integral_hasDerivAt_right`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`), the fact that continuous linear maps
commute with interval integrals (`ContinuousLinearMap.intervalIntegral_comp_comm`),
differentiability of the inner product (`HasDerivAt.inner`), and
`Dense.eq_of_inner_right`.
-/

namespace QPhys

open Complex MeasureTheory intervalIntegral
open scoped Classical

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The domain of the generator of a one-parameter group `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`.  We write the
derivative as `Complex.I • z`, so that `U t = exp (t • (I • A))`, i.e. `A` is the
"physicist's" generator (`U t = exp (i t A)`). -/

theorem genDom_of_adjoint {y z : H}
    (hyz : ∀ x ∈ genDom U, inner ℂ (gen U x) y = inner ℂ x z) :
    y ∈ genDom U ∧ gen U y = z := by
  set w : ℝ → H := fun s => (-Complex.I) • U (-s) z with hw
  have hwcont : Continuous w := by
    have : Continuous fun s : ℝ => U (-s) z := (hcont z).comp continuous_neg
    exact this.const_smul _
  have hwint : ∀ b c : ℝ, IntervalIntegrable w volume b c := fun b c =>
    hwcont.intervalIntegrable b c
  set W : ℝ → H := fun t => ∫ s in (0:ℝ)..t, w s with hW
  -- Step 1: the weak identity, tested against the (dense) domain
  have step1 : ∀ x ∈ genDom U, ∀ t : ℝ, inner ℂ x (U (-t) y - y) = inner ℂ x (W t) := by
    intro x hx t
    have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (inner ℂ (U r x) y : ℂ))
        (inner ℂ x (w s)) s := by
      intro s
      have h1 := (hasDerivAt_orbit hadd hx s).inner ℂ (hasDerivAt_const s y)
      have h2 : (inner ℂ (U s x) (0 : H) : ℂ) + inner ℂ (Complex.I • U s (gen U x)) y
          = inner ℂ x (w s) := by
        rw [inner_zero_right, zero_add, inner_smul_left, Complex.conj_I,
          (U_mem_genDom hadd hx s).2.symm, hyz _ (U_mem_genDom hadd hx s).1,
          hw]
        simp only [inner_smul_right]
        rw [inner_U_left h0 hadd hnorm]
      rwa [h2] at h1
    have hfint : IntervalIntegrable (fun s : ℝ => (inner ℂ x (w s) : ℂ)) volume 0 t := by
      exact (continuous_const.inner hwcont).intervalIntegrable 0 t
    have hsub : (∫ s in (0:ℝ)..t, (inner ℂ x (w s) : ℂ))
        = (inner ℂ (U t x) y : ℂ) - inner ℂ (U 0 x) y :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hfint
    have hpull : (∫ s in (0:ℝ)..t, (inner ℂ x (w s) : ℂ)) = inner ℂ x (W t) := by
      have := (innerSL ℂ x).intervalIntegral_comp_comm (a := (0:ℝ)) (b := t) (hwint 0 t)
      simpa [hW] using this
    rw [inner_sub_right, ← hpull, hsub, h0, ContinuousLinearMap.one_apply,
      inner_U_left h0 hadd hnorm]
  -- Step 2: hence the strong identity, by density
  have step2 : ∀ t : ℝ, U (-t) y - y = W t := by
    intro t
    refine (dense_genDom h0 hadd hcont).eq_of_inner_right ?_
    rintro ⟨x, hx⟩
    exact step1 x hx t
  -- Step 3: differentiate at `t = 0`
  have hWderiv : HasDerivAt W (w 0) 0 :=
    integral_hasDerivAt_right (hwint 0 0) (hwcont.stronglyMeasurableAtFilter _ _)
      hwcont.continuousAt
  have hgderiv : HasDerivAt (fun t : ℝ => U (-t) y) (w 0) 0 := by
    have hfun : (fun t : ℝ => U (-t) y) = fun t : ℝ => y + W t := by
      funext t
      rw [← step2 t]
      abel
    rw [hfun]
    simpa using hWderiv.const_add y
  have hw0 : w 0 = (-Complex.I) • z := by
    rw [hw]
    simp only [neg_zero]
    rw [h0, ContinuousLinearMap.one_apply]
  rw [hw0] at hgderiv
  refine mem_genDom_and_gen_eq ?_
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).neg
  have hg' : HasDerivAt (fun t : ℝ => U (-t) y) ((-Complex.I) • z) (-(0:ℝ)) := by
    rw [neg_zero]; exact hgderiv
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (h := fun t : ℝ => -t) (x := (0:ℝ)) hg' hneg
  have hfun2 : ((fun t : ℝ => U (-t) y) ∘ fun t : ℝ => -t) = fun t : ℝ => U t y := by
    funext t; simp
  rw [hfun2] at hcomp
  have hsmul : (-1 : ℝ) • ((-Complex.I) • z) = Complex.I • z := by
    rw [neg_one_smul, ← neg_smul, neg_neg]
  rwa [hsmul] at hcomp

end Generator

end

/-- **Stone's theorem** (self-adjointness of the generator).

Let `U : ℝ → H →L[ℂ] H` be a strongly continuous one-parameter unitary group on a complex
Hilbert space `H`.  Then its generator `A`, defined on
`D = {x | t ↦ U t x is differentiable at 0}` by `(d/dt) U t x |_{t = 0} = I • A x`
(i.e. `U t = exp (i t A)`), is a densely defined, linear, self-adjoint operator:

* `D` is a dense linear subspace;
* `A` is linear on `D`;
* `A` is symmetric: `⟪A x, y⟫ = ⟪x, A y⟫` for `x, y ∈ D`;
* `A` is maximal symmetric in the strong sense that `A* = A`: whenever `y, z` satisfy
  `⟪A x, y⟫ = ⟪x, z⟫` for all `x ∈ D`, then already `y ∈ D` and `A y = z`.
-/
