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

theorem gen_symmetric {x y : H} (hx : x ∈ genDom U) (hy : y ∈ genDom U) :
    inner ℂ (gen U x) y = inner ℂ x (gen U y) := by
  have hconst : HasDerivAt (fun t : ℝ => inner ℂ (U t x) (U t y)) 0 0 := by
    have : (fun t : ℝ => inner ℂ (U t x) (U t y)) = fun _ : ℝ => (inner ℂ x y : ℂ) := by
      funext t; exact inner_U_U hnorm t x y
    rw [this]
    exact hasDerivAt_const _ _
  have hd := (hasDerivAt_gen hx).inner ℂ (hasDerivAt_gen hy)
  have := hconst.unique hd
  rw [h0] at this
  simp only [ContinuousLinearMap.one_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at this
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : Complex.I * inner ℂ x (gen U y) = Complex.I * inner ℂ (gen U x) y := by
    linear_combination -this
  exact (mul_left_cancel₀ hI h2).symm

include h0 hadd hcont in
/-- The derivative at `0` of `h ↦ U h (∫ s in 0..a, U s x)`. -/
