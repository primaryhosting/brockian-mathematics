/-
/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *Hermitian* if
`⟪A x, y⟫ = ⟪x, A y⟫` for all vectors `x, y`. -/
def IsHermitian (A : E →ₗ[ℂ] E) : Prop :=
  ∀ x y : E, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ

/-- For a Hermitian operator `A` and an eigenvector `v` with eigenvalue `μ`, the
eigenvalue satisfies `conj μ = μ`. -/
theorem hermitian_conj_eigenvalue_eq_self
    {A : E →ₗ[ℂ] E} (hA : IsHermitian A) {μ : ℂ} {v : E} (hv : v ≠ 0)
    (heig : A v = μ • v) : (starRingEnd ℂ) μ = μ := by
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have key : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h1 : ⟪A v, v⟫_ℂ = (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_left]
    have h2 : ⟪v, A v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_right]
    rw [← h1, ← h2]
    exact hA v v
  exact mul_right_cancel₀ hvv key

/-- **Every eigenvalue of a Hermitian operator is real.**
If `A` is a Hermitian operator on a complex inner product space and `v ≠ 0`
satisfies `A v = μ • v`, then `μ` is a real number. -/
theorem hermitian_real_spectrum
    {A : E →ₗ[ℂ] E} (hA : IsHermitian A) {μ : ℂ} {v : E} (hv : v ≠ 0)
    (heig : A v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) := by
  refine ⟨μ.re, ?_⟩
  have h := hermitian_conj_eigenvalue_eq_self hA hv heig
  have : μ.im = 0 := by
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simpa using this)

/-- Matrix form: every eigenvalue of a Hermitian matrix is real. -/
theorem hermitian_matrix_real_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian) {μ : ℂ} {v : n → ℂ} (hv : v ≠ 0)
    (heig : M.mulVec v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) := by
  set w : EuclideanSpace ℂ n := WithLp.toLp 2 v with hw
  have hw0 : w ≠ 0 := by
    simp only [hw, ne_eq]
    intro h
    exact hv (by simpa using congrArg WithLp.ofLp h)
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hM
  have hherm : IsHermitian (Matrix.toEuclideanLin M) := fun x y => hsym x y
  have he : (Matrix.toEuclideanLin M) w = μ • w := by
    rw [Matrix.toLpLin_apply]
    simp [hw, heig]
  exact hermitian_real_spectrum hherm hw0 he

end QPhys

#print axioms QPhys.hermitian_real_spectrum
#print axioms QPhys.hermitian_matrix_real_spectrum

