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

theorem hasDerivAt_average (x : H) (a : ℝ) :
    HasDerivAt (fun h : ℝ => U h (∫ s in (0:ℝ)..a, U s x)) (U a x - x) 0 := by
  have hcx : Continuous fun s => U s x := hcont x
  have hint : ∀ b c : ℝ, IntervalIntegrable (fun s => U s x) volume b c := fun b c =>
    hcx.intervalIntegrable b c
  set F : ℝ → H := fun u => ∫ s in (0:ℝ)..u, U s x with hF
  have hFderiv : ∀ u : ℝ, HasDerivAt F (U u x) u := fun u =>
    integral_hasDerivAt_right (hint 0 u) (hcx.stronglyMeasurableAtFilter _ _) hcx.continuousAt
  have hfun : (fun h : ℝ => U h (∫ s in (0:ℝ)..a, U s x)) = fun h : ℝ => F (a + h) - F h := by
    funext h
    have h1 : U h (∫ s in (0:ℝ)..a, U s x) = ∫ s in (0:ℝ)..a, U h (U s x) :=
      ((U h).intervalIntegral_comp_comm (hint 0 a)).symm
    have h2 : (∫ s in (0:ℝ)..a, U h (U s x)) = ∫ s in (0:ℝ)..a, U (h + s) x := by
      simp_rw [U_apply_U hadd]
    have h3 : (∫ s in (0:ℝ)..a, U (h + s) x) = ∫ s in (h + 0)..(h + a), U s x :=
      integral_comp_add_left (fun s => U s x) h
    have h4 : F (a + h) - F h = ∫ s in h..(a + h), U s x :=
      integral_interval_sub_left (hint 0 (a + h)) (hint 0 h)
    rw [h1, h2, h3, h4, add_zero, add_comm h a]
  rw [hfun]
  have hA : HasDerivAt (fun h : ℝ => F (a + h)) (U a x) 0 := by
    have h1 : HasDerivAt F (U a x) (a + 0) := by rw [add_zero]; exact hFderiv a
    have h2 : HasDerivAt (fun h : ℝ => a + h) 1 (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add a
    simpa using HasDerivAt.scomp (𝕜 := ℝ) (h := fun h : ℝ => a + h) (x := 0) h1 h2
  have hB : HasDerivAt F x 0 := by
    have := hFderiv 0
    rwa [h0, ContinuousLinearMap.one_apply] at this
  exact hA.sub hB

include h0 hadd hcont in
/-- Averages of the orbit lie in the domain of the generator. -/
