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

open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    qform A x = ∑ i, hA.eigenvalues i * ‖(hA.eigenvectorBasis.repr x).ofLp i‖ ^ 2 := by
  have h : (inner ℂ x (Matrix.toLpLin 2 2 A x) : ℂ)
      = ∑ i, ((hA.eigenvalues i * ‖(hA.eigenvectorBasis.repr x).ofLp i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hA.eigenvectorBasis.repr.inner_map_map x (Matrix.toLpLin 2 2 A x), PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_toLpLin hA x i, RCLike.inner_apply]
    have hmul : (hA.eigenvalues i : ℂ) * (hA.eigenvectorBasis.repr x).ofLp i
          * (starRingEnd ℂ) ((hA.eigenvectorBasis.repr x).ofLp i)
        = (hA.eigenvalues i : ℂ) * ((hA.eigenvectorBasis.repr x).ofLp i
          * (starRingEnd ℂ) ((hA.eigenvectorBasis.repr x).ofLp i)) := by ring
    rw [hmul, Complex.mul_conj']
    push_cast
    ring
  rw [qform, h, Complex.re_sum]
  simp only [Complex.ofReal_re]

