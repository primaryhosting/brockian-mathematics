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

def genDom (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0}
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    refine ⟨z + w, ?_⟩
    have : (fun t => U t (x + y)) = fun t => U t x + U t y := by
      funext t; simp
    rw [this, smul_add]
    exact hz.add hw
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp only [map_zero, smul_zero]
    exact hasDerivAt_const _ _
  smul_mem' := by
    rintro c x ⟨z, hz⟩
    refine ⟨c • z, ?_⟩
    have : (fun t => U t (c • x)) = fun t => c • U t x := by
      funext t; simp
    rw [this, smul_comm]
    exact hz.const_smul c

/-- The generator `A` of a one-parameter group: `A x` is the unique `z` with
`(d/dt) U t x |_{t=0} = I • z`, and `0` off the domain. -/
