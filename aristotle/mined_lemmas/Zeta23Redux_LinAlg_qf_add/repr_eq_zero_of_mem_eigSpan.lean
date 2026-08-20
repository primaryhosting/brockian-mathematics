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

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/

lemma repr_eq_zero_of_mem_eigSpan (hM : M.IsHermitian) {s : Finset (Fin d)}
    {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ eigSpan hM s) {j : Fin d} (hj : j ∉ s) :
    hM.eigenvectorBasis.repr x j = 0 := by
  have hle : eigSpan hM s ≤ LinearMap.ker
      ((EuclideanSpace.proj (𝕜 := ℂ) j).toLinearMap.comp
        (hM.eigenvectorBasis.repr.toLinearEquiv.toLinearMap)) := by
    rw [eigSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hij : (i : Fin d) ≠ j := fun h => hj (h ▸ i.2)
    simp [LinearMap.mem_ker, OrthonormalBasis.repr_self, EuclideanSpace.single_apply,
      Ne.symm hij]
  simpa using hle hx

/-- On the span of eigenvectors whose eigenvalues are at most `c`, the quadratic form is bounded
by `c * ‖x‖ ^ 2`. -/
