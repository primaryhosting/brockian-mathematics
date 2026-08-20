-- Note: Lean 4 requires `import` commands to precede any doc comment, so the requested
-- header block appears immediately below the import.
import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Submodule Module.End Matrix

namespace QPhys

/-- Two commuting symmetric (Hermitian) operators on a finite-dimensional inner product space
have a common orthonormal eigenbasis, indexed by any index type of the right cardinality. -/

theorem commuting_simultaneous {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ a b : n → ℝ,
      star U * A * U = Matrix.diagonal (fun i => (a i : ℂ)) ∧
      star U * B * U = Matrix.diagonal (fun i => (b i : ℂ)) := by
  classical
  set A' := Matrix.toEuclideanLin A with hA'def
  set B' := Matrix.toEuclideanLin B with hB'def
  have hA' : A'.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hB' : B'.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hB
  have hAB' : Commute A' B' := by
    have h : A * B = B * A := hAB
    refine LinearMap.ext fun x => ?_
    show Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x)
      = Matrix.toEuclideanLin B (Matrix.toEuclideanLin A x)
    apply WithLp.toLp_injective (p := 2)
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, h]
  obtain ⟨v, hv⟩ := exists_orthonormalBasis_joint_eigenvectors
    (ι := n) finrank_euclideanSpace hA' hB' hAB'
  choose μ hμ using fun i => (hv i).1
  choose ν hν using fun i => (hv i).2
  -- the eigenvalues are real
  have hreal : ∀ (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n), T.IsSymmetric →
      ∀ (i : n) (c : ℂ), T (v i) = c • v i → ((RCLike.re c : ℝ) : ℂ) = c := by
    intro T hT i c hc
    have hne : (v i : EuclideanSpace ℂ n) ≠ 0 := v.toBasis.ne_zero i
    have hev : Module.End.HasEigenvalue T c :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hc, hne⟩
    exact RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hev)
  have hmul : ∀ (M : Matrix n n ℂ) (i : n) (c : ℂ),
      Matrix.toEuclideanLin M (v i) = c • v i → M *ᵥ ⇑(v i) = c • ⇑(v i) := by
    intro M i c hc
    have := congrArg (fun x : EuclideanSpace ℂ n => WithLp.ofLp x) hc
    simpa [Matrix.ofLp_toLpLin] using this
  refine ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix v.toBasis,
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary v,
    fun i => RCLike.re (μ i), fun i => RCLike.re (ν i), ?_, ?_⟩
  · refine conjugate_eq_diagonal_of_eigenvectors v A _ fun j => ?_
    rw [hreal A' hA' j (μ j) (hμ j)]
    exact hmul A j (μ j) (hμ j)
  · refine conjugate_eq_diagonal_of_eigenvectors v B _ fun j => ?_
    rw [hreal B' hB' j (ν j) (hν j)]
    exact hmul B j (ν j) (hν j)

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

