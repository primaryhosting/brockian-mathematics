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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped BigOperators

namespace Zeta23Redux.LinAlg

section Aux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real part of the) Hermitian quadratic form `x ↦ x* M x`. -/
private noncomputable def qform (M : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ M *ᵥ x).re

/-- The squared euclidean norm of a vector. -/
private noncomputable def nsq (x : n → ℂ) : ℝ := (star x ⬝ᵥ x).re

omit [DecidableEq n] in

private lemma nsq_eq_sum (x : n → ℂ) : nsq x = ∑ i, ‖x i‖ ^ 2 := by
  simp only [nsq, dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

omit [DecidableEq n] in
