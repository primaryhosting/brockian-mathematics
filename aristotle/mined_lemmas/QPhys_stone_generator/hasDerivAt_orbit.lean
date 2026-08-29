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

theorem hasDerivAt_orbit {x : H} (hx : x ∈ genDom U) (t : ℝ) :
    HasDerivAt (fun s => U s x) (Complex.I • U t (gen U x)) t := by
  have h1 : HasDerivAt (fun s => U s (U t x)) (Complex.I • gen U (U t x)) 0 :=
    hasDerivAt_gen (U_mem_genDom hadd hx t).1
  rw [(U_mem_genDom hadd hx t).2] at h1
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h1' : HasDerivAt (fun s => U s (U t x)) (Complex.I • U t (gen U x)) (t - t) := by
    rw [sub_self]; exact h1
  have h3 := HasDerivAt.scomp (𝕜 := ℝ) (h := fun s : ℝ => s - t) (x := t) h1' h2
  have key : ((fun s => U s (U t x)) ∘ fun s : ℝ => s - t) = fun s => U s x := by
    funext s
    simp only [Function.comp_apply]
    rw [U_apply_U hadd, sub_add_cancel]
  rw [key] at h3
  simpa using h3

omit [CompleteSpace H] in
include h0 hnorm in
/-- The generator is symmetric. -/
