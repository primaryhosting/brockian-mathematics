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

theorem stone_generator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = (U s).comp (U t)) (hnorm : ∀ t x, ‖U t x‖ = ‖x‖)
    (hcont : ∀ x : H, Continuous fun t => U t x) :
    ∃ (D : Submodule ℂ H) (A : H → H),
      -- `D` is the domain of the generator
      (∀ x, x ∈ D ↔ ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0) ∧
      -- `A` implements the derivative on `D`
      (∀ x ∈ D, HasDerivAt (fun t => U t x) (Complex.I • A x) 0) ∧
      -- `D` is dense
      Dense (D : Set H) ∧
      -- `A` is linear on `D`
      (∀ (c : ℂ), ∀ x ∈ D, ∀ y ∈ D, A (c • x + y) = c • A x + A y) ∧
      -- `A` is symmetric
      (∀ x ∈ D, ∀ y ∈ D, inner ℂ (A x) y = inner ℂ x (A y)) ∧
      -- `A` is self-adjoint: the domain of the adjoint is contained in `D`
      (∀ y z : H, (∀ x ∈ D, inner ℂ (A x) y = inner ℂ x z) → y ∈ D ∧ A y = z) := by
  refine ⟨genDom U, gen U, fun x => Iff.rfl, fun x hx => hasDerivAt_gen hx,
    dense_genDom h0 hadd hcont, ?_, fun x hx y hy => gen_symmetric h0 hnorm hx hy,
    fun y z hyz => genDom_of_adjoint h0 hadd hnorm hcont hyz⟩
  intro c x hx y hy
  refine gen_eq ?_
  have hfun : (fun t => U t (c • x + y)) = fun t => c • U t x + U t y := by
    funext t; simp
  rw [hfun, smul_add, smul_comm]
  exact ((hasDerivAt_gen hx).const_smul c).add (hasDerivAt_gen hy)

/-- Sanity check: the hypotheses of `stone_generator` are satisfiable (they hold for the
unitary group `U t = e^{i t}` on `H = ℂ`), so the theorem is not vacuous. -/
example : ∃ (U : ℝ → ℂ →L[ℂ] ℂ), (U 0 = 1) ∧ (∀ s t, U (s + t) = (U s).comp (U t)) ∧
    (∀ t x, ‖U t x‖ = ‖x‖) ∧ (∀ x : ℂ, Continuous fun t => U t x) := by
  refine ⟨fun t => (Complex.exp (t * Complex.I)) • (1 : ℂ →L[ℂ] ℂ), by simp, ?_, ?_, ?_⟩
  · intro s t
    ext
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, Complex.ofReal_add,
      mul_one]
    rw [← Complex.exp_add]
    ring_nf
  · intro t x
    simp [Complex.norm_exp]
  · intro x
    have : Continuous fun t : ℝ => Complex.exp (t * Complex.I) * x := by fun_prop
    simpa using this

end QPhys

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

