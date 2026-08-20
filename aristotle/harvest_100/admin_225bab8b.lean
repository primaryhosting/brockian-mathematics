import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped InnerProductSpace
open RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every eigenvalue of a Hermitian operator is real.**

`T : E →ₗ[ℂ] E` is Hermitian (symmetric): `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`.
If `μ : ℂ` is an eigenvalue of `T`, i.e. there is a nonzero `v` with `T v = μ • v`,
then `μ` is real: `μ = (r : ℂ)` for some `r : ℝ`. -/
theorem hermitian_real_spectrum {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (heig : T v = μ • v) :
    ∃ r : ℝ, μ = (r : ℂ) := by
  have hn : ((‖v‖ : ℂ)) ^ 2 ≠ 0 := by
    simp [norm_eq_zero, hv]
  have key : ((‖v‖ : ℂ)) ^ 2 * (starRingEnd ℂ) μ = μ * ((‖v‖ : ℂ)) ^ 2 := by
    have := hT v v
    rw [heig] at this
    simpa [inner_smul_left, inner_smul_right] using this
  have hμ : (starRingEnd ℂ) μ = μ := by
    have := key.trans (mul_comm μ _)
    exact mul_left_cancel₀ hn this
  exact ⟨μ.re, (Complex.conj_eq_iff_re.mp hμ).symm⟩

/-- Restatement in terms of Mathlib's `LinearMap.IsSymmetric` and
`Module.End.HasEigenvalue`: the eigenvalues of a Hermitian operator are real.
This follows from `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem hermitian_real_spectrum' {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue T μ) : ∃ r : ℝ, μ = (r : ℂ) := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  exact hermitian_real_spectrum hT hv₂ (Module.End.mem_eigenspace_iff.mp hv₁)

/-- Corollary for bounded (continuous) self-adjoint operators, the usual setting for
quantum-mechanical observables: every eigenvalue is real. -/
theorem selfAdjoint_real_spectrum [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (heig : T v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) :=
  hermitian_real_spectrum hT.isSymmetric hv heig

/-- Corollary for Hermitian matrices: every eigenvalue of a Hermitian matrix is real. -/
theorem hermitianMatrix_real_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {μ : ℂ} {v : n → ℂ} (hv : v ≠ 0)
    (heig : A.mulVec v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) := by
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hA
  refine hermitian_real_spectrum hsym (v := (WithLp.toLp 2 v)) ?_ ?_
  · simpa using hv
  · ext i
    simpa [Matrix.toLpLin_apply] using congrFun heig i

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

