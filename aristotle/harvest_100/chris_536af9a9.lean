import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The uncertainty (standard deviation) of a symmetric operator `A` in the state `ψ`:
the norm of `A ψ` after subtracting its expectation value `⟪ψ, A ψ⟫`. -/
noncomputable def uncertainty (A : E →ₗ[ℂ] E) (psi : E) : ℝ :=
  ‖A psi - (⟪psi, A psi⟫_ℂ) • psi‖

/-- **Heisenberg uncertainty principle.**

For a normalized state `psi` in a complex inner product space and two symmetric
(formally self-adjoint) operators `X`, `P` satisfying the canonical commutation relation
`[X, P] psi = i ℏ psi`, we have `Δx · Δp ≥ ℏ / 2`.

The proof is the standard one: the commutator identity gives
`⟪u, v⟫ - ⟪v, u⟫ = i ℏ` for the mean-subtracted vectors `u = (X - ⟨X⟩) psi`,
`v = (P - ⟨P⟩) psi`, so `ℏ = 2 * Im ⟪u, v⟫ ≤ 2 * ‖⟪u, v⟫‖`, and Cauchy–Schwarz
(`norm_inner_le_norm`) bounds `‖⟪u, v⟫‖ ≤ ‖u‖ * ‖v‖`. -/
theorem heisenberg_uncertainty (X P : E →ₗ[ℂ] E) (psi : E) (hpsi : ‖psi‖ = 1)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (hcomm : X (P psi) - P (X psi) = (Complex.I * hbar) • psi) :
    uncertainty X psi * uncertainty P psi ≥ hbar / 2 := by
  set a : ℂ := ⟪psi, X psi⟫_ℂ
  set b : ℂ := ⟪psi, P psi⟫_ℂ
  set u : E := X psi - a • psi with hu
  set v : E := P psi - b • psi with hv
  -- expand the two inner products
  have hXs : ⟪X psi, psi⟫_ℂ = a := hX psi psi
  have hPs : ⟪P psi, psi⟫_ℂ = b := hP psi psi
  have hnorm : ⟪psi, psi⟫_ℂ = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) psi
    rw [this, hpsi]
    norm_num
  have huv : ⟪u, v⟫_ℂ = ⟪X psi, P psi⟫_ℂ - a * b := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hXs, hnorm]
    ring
  have hvu : ⟪v, u⟫_ℂ = ⟪P psi, X psi⟫_ℂ - b * a := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hPs, hnorm]
    ring
  have hcomm' : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    have h1 : ⟪X psi, P psi⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ := hX psi (P psi)
    have h2 : ⟪P psi, X psi⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ := hP psi (X psi)
    rw [h1, h2, ← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  have key : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * hbar := by
    rw [huv, hvu, ← hcomm']; ring
  -- hence `hbar = 2 * Im ⟪u, v⟫`
  have himsym : ⟪v, u⟫_ℂ = (starRingEnd ℂ) ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have him : (2 : ℝ) * (⟪u, v⟫_ℂ).im = hbar := by
    have h := congrArg Complex.im key
    rw [himsym, Complex.sub_im, Complex.conj_im] at h
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] at h
    linarith
  have hle : hbar ≤ 2 * ‖⟪u, v⟫_ℂ‖ := by
    rw [← him]
    have : (⟪u, v⟫_ℂ).im ≤ ‖⟪u, v⟫_ℂ‖ := Complex.im_le_norm _
    linarith
  have hcs : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar ≤ 2 * (‖u‖ * ‖v‖) := le_trans hle (by linarith)
  simp only [uncertainty, ge_iff_le]
  linarith

/-!
## A concrete model: the hypotheses are consistent and the bound is sharp

Spin-1/2: on `EuclideanSpace ℂ (Fin 2)` take `X = σx`, `P = σy` (both Hermitian) and the
state `psi = |↑⟩`.  Then `[X, P] psi = 2 i psi`, i.e. the canonical commutation relation
holds with `ℏ = 2`, and both uncertainties equal `1`, so `Δx · Δp = 1 = ℏ / 2`:
the Heisenberg bound is attained.
-/

namespace SpinExample

/-- The Pauli matrix `σx`, as an operator on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def sigmaX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 1; 1, 0]

/-- The Pauli matrix `σy`, as an operator on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def sigmaY : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, -Complex.I; Complex.I, 0]

/-- The spin-up state. -/
noncomputable def up : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 (1 : ℂ)

lemma norm_up : ‖up‖ = 1 := by simp [up]

lemma sigmaX_symm (u v : EuclideanSpace ℂ (Fin 2)) : ⟪sigmaX u, v⟫_ℂ = ⟪u, sigmaX v⟫_ℂ := by
  simp [sigmaX, Matrix.toEuclideanLin, PiLp.inner_apply, Fin.sum_univ_two, dotProduct]
  ring

lemma sigmaY_symm (u v : EuclideanSpace ℂ (Fin 2)) : ⟪sigmaY u, v⟫_ℂ = ⟪u, sigmaY v⟫_ℂ := by
  simp [sigmaY, Matrix.toEuclideanLin, PiLp.inner_apply, Fin.sum_univ_two, dotProduct]
  ring

/-- The canonical commutation relation `[σx, σy] |↑⟩ = i · 2 · |↑⟩`. -/
lemma commutator_up :
    sigmaX (sigmaY up) - sigmaY (sigmaX up) = (Complex.I * ((2 : ℝ) : ℂ)) • up := by
  ext i
  fin_cases i
  · simp [sigmaX, sigmaY, up, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply]
    ring
  · simp [sigmaX, sigmaY, up, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two,
      EuclideanSpace.single_apply]

lemma uncertainty_sigmaX : uncertainty sigmaX up = 1 := by
  have h : (⟪up, sigmaX up⟫_ℂ) = 0 := by
    simp [up, sigmaX, Matrix.toEuclideanLin, PiLp.inner_apply, EuclideanSpace.single_apply]
  rw [uncertainty, h]
  simp [up, sigmaX, Matrix.toEuclideanLin, EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma uncertainty_sigmaY : uncertainty sigmaY up = 1 := by
  have h : (⟪up, sigmaY up⟫_ℂ) = 0 := by
    simp [up, sigmaY, Matrix.toEuclideanLin, PiLp.inner_apply, EuclideanSpace.single_apply]
  rw [uncertainty, h]
  simp [up, sigmaY, Matrix.toEuclideanLin, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- In this model the hypotheses of `QPhys.heisenberg_uncertainty` hold with `ℏ = 2`
and the bound is attained: `Δx · Δp = 1 = ℏ / 2`. -/
theorem heisenberg_sharp :
    uncertainty sigmaX up * uncertainty sigmaY up = (2 : ℝ) / 2 := by
  rw [uncertainty_sigmaX, uncertainty_sigmaY]; norm_num

/-- Sanity check: the general theorem applies to this model. -/
example : uncertainty sigmaX up * uncertainty sigmaY up ≥ (2 : ℝ) / 2 :=
  heisenberg_uncertainty sigmaX sigmaY up norm_up sigmaX_symm sigmaY_symm 2 commutator_up

end SpinExample

end QPhys

import Mathlib
import RequestProject.Heisenberg

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

