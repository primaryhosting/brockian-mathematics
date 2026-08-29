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

noncomputable def gen (U : ℝ → H →L[ℂ] H) (x : H) : H :=
  if h : ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0 then h.choose else 0

variable {U : ℝ → H →L[ℂ] H}

omit [CompleteSpace H] in
