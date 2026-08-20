/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file proves **Uhlmann's theorem**: for positive semidefinite states `ρ`, `σ` on `ℂ^n`,
the fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` is the *maximal* overlap `|⟪ψ, φ⟫|` taken over all
purifications `ψ` of `ρ` and `φ` of `σ` in `ℂ^n ⊗ ℂ^n`, where a purification of `ρ` is a
vector whose reduced density matrix (partial trace over the second factor) is `ρ`.

Neither quantum fidelity nor purifications (nor even the polar decomposition of a matrix)
are available in Mathlib, so everything is developed here from scratch:

* `QI.abs_trace_conjTranspose_mul_le`: Cauchy–Schwarz/AM–GM for the Hilbert–Schmidt
  inner product, `|Tr (Aᴴ B)| ≤ (‖A‖₂² + ‖B‖₂²) / 2`.
* `QI.exists_unitary_polar`: the polar decomposition `M = √(M Mᴴ) U` with `U` unitary,
  obtained by extending the isometry `√(M Mᴴ) x ↦ Mᴴ x` to a unitary of `ℂ^n`.
* `QI.norm_trace_mul_unitary_le`: `|Tr (Q Y)| ≤ Tr Q` for `Q ≥ 0` and `Y` unitary.
* `QI.uhlmann_fidelity_matrix` and `QI.uhlmann_fidelity`: Uhlmann's theorem, in matrix
  form and in terms of purifying vectors.
-/

open scoped MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Hilbert–Schmidt (Frobenius) inner product -/

/-- The squared Frobenius (Hilbert–Schmidt) norm of a matrix. -/

theorem exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, U * Uᴴ = 1 ∧ M = CFC.sqrt (M * Mᴴ) * U := by
  have hPSD : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  set P := CFC.sqrt (M * Mᴴ) with hPdef
  have hPP : P * P = M * Mᴴ := CFC.sqrt_mul_sqrt_self _ hPSD.nonneg
  have hPH : Pᴴ = P := (CFC.sqrt_nonneg (M * Mᴴ)).posSemidef.isHermitian
  set p := Matrix.toEuclideanLin P with hpdef
  set m := Matrix.toEuclideanLin Mᴴ with hmdef
  have hadjp : LinearMap.adjoint p = p := by
    rw [hpdef, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hPH]
  have hadjm : LinearMap.adjoint m = Matrix.toEuclideanLin M := by
    rw [hmdef, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_conjTranspose]
  -- `√(M Mᴴ)` and `Mᴴ` have the same "length function", hence the same kernel
  have hnorm : ∀ x, ‖p x‖ = ‖m x‖ := by
    intro x
    have hcomp : p (p x) = Matrix.toEuclideanLin M (m x) := by
      have h1 : Matrix.toEuclideanLin (P * P) = p.comp p := Matrix.toLpLin_mul 2 2 2 P P
      have h2 : Matrix.toEuclideanLin (M * Mᴴ) = (Matrix.toEuclideanLin M).comp m :=
        Matrix.toLpLin_mul 2 2 2 M Mᴴ
      have h3 := hPP ▸ h1
      rw [h2] at h3
      exact congrArg (fun L => L x) h3.symm
    have hinner : (inner (𝕜 := ℂ) (p x) (p x)) = inner (𝕜 := ℂ) (m x) (m x) := by
      rw [← LinearMap.adjoint_inner_left p x (p x), hadjp, hcomp, ← hadjm,
        LinearMap.adjoint_inner_left m x (m x)]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner]
  have hker : LinearMap.ker p = LinearMap.ker m := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      exact norm_eq_zero.1 (by rw [← hnorm x, hx, norm_zero])
    · intro hx
      exact norm_eq_zero.1 (by rw [hnorm x, hx, norm_zero])
  -- the isometry `P x ↦ Mᴴ x` on the range of `P`
  set f₀ := Submodule.liftQ (LinearMap.ker p) m (le_of_eq hker) with hf₀
  set f : LinearMap.range p →ₗ[ℂ] EuclideanSpace ℂ n :=
    f₀.comp (p.quotKerEquivRange.symm : LinearMap.range p →ₗ[ℂ] _) with hfdef
  have hfapp : ∀ x : EuclideanSpace ℂ n, f ⟨p x, ⟨x, rfl⟩⟩ = m x := by
    intro x
    have h1 : p.quotKerEquivRange.symm ⟨p x, ⟨x, rfl⟩⟩ = (LinearMap.ker p).mkQ x :=
      LinearMap.quotKerEquivRange_symm_apply_image p x ⟨x, rfl⟩
    simp only [hfdef, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hf₀,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hf : ∀ y : LinearMap.range p, ‖f y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [hfapp x]
    exact (hnorm x).symm
  set L : LinearMap.range p →ₗᵢ[ℂ] EuclideanSpace ℂ n := ⟨f, hf⟩ with hL
  set g := L.extend with hgdef
  have hg : ∀ x, g (p x) = m x := by
    intro x
    have h := L.extend_apply ⟨p x, ⟨x, rfl⟩⟩
    rw [hgdef]
    simpa [hL, hfapp x] using h
  set G := Matrix.toEuclideanLin.symm g.toLinearMap with hGdef
  have hGL : Matrix.toEuclideanLin G = g.toLinearMap := by
    rw [hGdef, LinearEquiv.apply_symm_apply]
  have hGP : G * P = Mᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2 G P, ← hmdef]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, hGL]
    exact hg x
  have hGG : Gᴴ * G = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul 2 2 2 Gᴴ G, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hGL]
    refine LinearMap.ext fun x => ?_
    apply ext_inner_right ℂ
    intro y
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    show inner ℂ (g x) (g y) = _
    rw [g.inner_map_map]
    simp
  refine ⟨Gᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose, hGG]
  · have h := congrArg Matrix.conjTranspose hGP
    rw [Matrix.conjTranspose_mul, hPH, Matrix.conjTranspose_conjTranspose] at h
    exact h.symm

/-- For a positive semidefinite `Q` and a unitary `Y`, `|Tr (Q Y)| ≤ Tr Q`. -/
