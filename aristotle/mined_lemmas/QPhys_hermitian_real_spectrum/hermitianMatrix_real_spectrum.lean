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

