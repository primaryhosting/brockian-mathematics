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
noncomputable def frobSq (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq n] in
lemma frobSq_nonneg (A : Matrix n n ℂ) : 0 ≤ frobSq A := by
  unfold frobSq
  positivity

omit [DecidableEq n] in
lemma trace_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (Aᴴ * A).trace = (frobSq A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    frobSq, Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

omit [DecidableEq n] in
/-- Cauchy–Schwarz together with AM–GM for the Hilbert–Schmidt inner product. -/
lemma abs_trace_conjTranspose_mul_le (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ (frobSq A + frobSq B) / 2 := by
  have h : (Aᴴ * B).trace = ∑ i, ∑ j, star (A j i) * B j i := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  calc ‖∑ i, ∑ j, star (A j i) * B j i‖ ≤ ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by simp)
    _ ≤ ∑ i, ∑ j, (‖A j i‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        nlinarith [sq_nonneg (‖A j i‖ - ‖B j i‖)]
    _ = (frobSq A + frobSq B) / 2 := by
        rw [frobSq, frobSq, Finset.sum_comm (f := fun i j => ‖A i j‖ ^ 2),
          Finset.sum_comm (f := fun i j => ‖B i j‖ ^ 2)]
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

/-! ## Polar decomposition -/

/-- **Polar decomposition** of a square complex matrix: `M = √(M Mᴴ) U` for some unitary `U`.

The unitary is produced by extending the isometry `√(M Mᴴ) x ↦ Mᴴ x`, defined on the range
of `√(M Mᴴ)`, to a linear isometry of the whole space. -/
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
lemma norm_trace_mul_unitary_le {Q Y : Matrix n n ℂ} (hQ : Q.PosSemidef) (hY : Y * Yᴴ = 1) :
    ‖(Q * Y).trace‖ ≤ Q.trace.re := by
  set R := CFC.sqrt Q with hRdef
  have hRPSD : R.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hRH : Rᴴ = R := hRPSD.isHermitian
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  have htr : ((Q.trace.re : ℝ) : ℂ) = Q.trace := by
    have h0 : 0 ≤ Q.trace := hQ.trace_nonneg
    rw [Complex.nonneg_iff] at h0
    rw [Complex.ext_iff]
    exact ⟨rfl, by simpa using h0.2⟩
  have hfR : frobSq R = Q.trace.re := by
    have h1 : ((frobSq R : ℝ) : ℂ) = ((Q.trace.re : ℝ) : ℂ) := by
      rw [← trace_conjTranspose_mul_self, hRH, hRR, htr]
    exact_mod_cast h1
  have hfRY : frobSq (R * Y) = Q.trace.re := by
    have h1 : ((frobSq (R * Y) : ℝ) : ℂ) = ((Q.trace.re : ℝ) : ℂ) := by
      rw [← trace_conjTranspose_mul_self, Matrix.conjTranspose_mul, hRH, htr]
      calc (Yᴴ * R * (R * Y)).trace = (Yᴴ * (R * R) * Y).trace := by
            rw [show Yᴴ * R * (R * Y) = Yᴴ * (R * R) * Y by noncomm_ring]
        _ = (Q * (Y * Yᴴ)).trace := by
            rw [hRR, show Yᴴ * Q * Y = Yᴴ * (Q * Y) by noncomm_ring, Matrix.trace_mul_comm]
            congr 1; noncomm_ring
        _ = Q.trace := by rw [hY, Matrix.mul_one]
    exact_mod_cast h1
  have hbound := abs_trace_conjTranspose_mul_le R (R * Y)
  rw [hRH, ← Matrix.mul_assoc, hRR, hfR, hfRY] at hbound
  linarith

/-! ## Fidelity and purifications -/

/-- The (Uhlmann) fidelity of two states `ρ`, `σ`, i.e. `Tr √(√ρ σ √ρ)`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

/-- Sanity check: the fidelity of a state with itself is its trace (so `F(ρ, ρ) = 1`
for a density matrix `ρ`). -/
lemma fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : fidelity ρ ρ = ρ.trace.re := by
  have hs : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have h1 : CFC.sqrt ρ * ρ * CFC.sqrt ρ = ρ ^ 2 := by
    calc CFC.sqrt ρ * ρ * CFC.sqrt ρ
        = CFC.sqrt ρ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt ρ := by rw [hs]
      _ = (CFC.sqrt ρ * CFC.sqrt ρ) * (CFC.sqrt ρ * CFC.sqrt ρ) := by noncomm_ring
      _ = ρ ^ 2 := by rw [hs, sq]
  rw [fidelity, h1, CFC.sqrt_sq ρ hρ.nonneg]

/-- The reduced density matrix (partial trace over the second tensor factor) of a
vector `ψ` of `ℂ^n ⊗ ℂ^n`, viewed as a function on `n × n`. -/
noncomputable def ptrace (ψ : n × n → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, ψ (i, k) * star (ψ (j, k))

/-- The matrix associated to a vector of `ℂ^n ⊗ ℂ^n`. -/
noncomputable def toMat (ψ : n × n → ℂ) : Matrix n n ℂ := Matrix.of fun i k => ψ (i, k)

omit [DecidableEq n] in
lemma ptrace_eq_mul_conjTranspose (ψ : n × n → ℂ) :
    ptrace ψ = toMat ψ * (toMat ψ)ᴴ := by
  ext i j
  simp [ptrace, toMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
lemma overlap_eq_trace (ψ φ : n × n → ℂ) :
    ∑ p, star (ψ p) * φ p = ((toMat ψ)ᴴ * toMat φ).trace := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    toMat, Matrix.of_apply]
  exact Finset.sum_comm

/-! ## Uhlmann's theorem -/

section Main

variable {ρ σ : Matrix n n ℂ}

/-- With `M = √ρ √σ` one has `M Mᴴ = √ρ σ √ρ`, so `√(M Mᴴ)` is the matrix whose trace
is the fidelity. -/
lemma sqrt_mul_sqrt_mul_conjTranspose (hσ : σ.PosSemidef) :
    (CFC.sqrt ρ * CFC.sqrt σ) * (CFC.sqrt ρ * CFC.sqrt σ)ᴴ = CFC.sqrt ρ * σ * CFC.sqrt ρ := by
  have hsrH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hssH : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have hssss : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  rw [Matrix.conjTranspose_mul, hsrH, hssH]
  calc CFC.sqrt ρ * CFC.sqrt σ * (CFC.sqrt σ * CFC.sqrt ρ)
      = CFC.sqrt ρ * (CFC.sqrt σ * CFC.sqrt σ) * CFC.sqrt ρ := by noncomm_ring
    _ = CFC.sqrt ρ * σ * CFC.sqrt ρ := by rw [hssss]

lemma fidelity_nonneg (hσ : σ.PosSemidef) : 0 ≤ fidelity ρ σ := by
  have hS : (CFC.sqrt ρ * σ * CFC.sqrt ρ).PosSemidef := by
    have hsrH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
    have := hσ.conjTranspose_mul_mul_same (B := CFC.sqrt ρ)
    rwa [hsrH] at this
  have h0 : 0 ≤ (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace :=
    (CFC.sqrt_nonneg _).posSemidef.trace_nonneg
  rw [Complex.nonneg_iff] at h0
  exact h0.1

/-- Every overlap of purifications is bounded by the fidelity. -/
lemma overlap_le_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (A B : Matrix n n ℂ) (hA : A * Aᴴ = ρ) (hB : B * Bᴴ = σ) :
    ‖(Aᴴ * B).trace‖ ≤ fidelity ρ σ := by
  set sr := CFC.sqrt ρ with hsrdef
  set ss := CFC.sqrt σ with hssdef
  have hsrH : srᴴ = sr := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  -- polar decompositions of the two purifications
  obtain ⟨U, hU, hAU⟩ := exists_unitary_polar A
  obtain ⟨V, hV, hBV⟩ := exists_unitary_polar B
  rw [hA] at hAU
  rw [hB] at hBV
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  -- polar decomposition of `√ρ √σ`
  obtain ⟨W, hW, hMW⟩ := exists_unitary_polar (sr * ss)
  rw [sqrt_mul_sqrt_mul_conjTranspose hσ] at hMW
  set Q := CFC.sqrt (sr * σ * sr) with hQdef
  have hQPSD : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  set Y := W * V * Uᴴ with hYdef
  have hYH : Yᴴ = U * Vᴴ * Wᴴ := by
    rw [hYdef]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hYY : Y * Yᴴ = 1 := by
    rw [hYdef, hYH]
    calc W * V * Uᴴ * (U * Vᴴ * Wᴴ)
        = W * V * (Uᴴ * U) * Vᴴ * Wᴴ := by noncomm_ring
      _ = W * (V * Vᴴ) * Wᴴ := by rw [hUU]; noncomm_ring
      _ = 1 := by rw [hV, Matrix.mul_one, hW]
  have htrace : (Aᴴ * B).trace = (Q * Y).trace := by
    rw [hAU, hBV, Matrix.conjTranspose_mul, hsrH]
    calc (Uᴴ * sr * (ss * V)).trace = ((sr * ss) * V * Uᴴ).trace := by
          rw [show Uᴴ * sr * (ss * V) = Uᴴ * (sr * ss * V) by noncomm_ring,
            Matrix.trace_mul_comm]
          congr 1; noncomm_ring
      _ = (Q * Y).trace := by rw [hMW, hYdef]; congr 1; noncomm_ring
  rw [htrace]
  exact norm_trace_mul_unitary_le hQPSD hYY

/-- The fidelity is attained by a pair of purifications. -/
lemma exists_overlap_eq_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧
      fidelity ρ σ = ‖(Aᴴ * B).trace‖ := by
  set sr := CFC.sqrt ρ with hsrdef
  set ss := CFC.sqrt σ with hssdef
  have hsrH : srᴴ = sr := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hssH : ssᴴ = ss := (CFC.sqrt_nonneg σ).posSemidef.isHermitian
  have hsrsr : sr * sr = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hssss : ss * ss = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  obtain ⟨W, hW, hMW⟩ := exists_unitary_polar (sr * ss)
  rw [sqrt_mul_sqrt_mul_conjTranspose hσ] at hMW
  set Q := CFC.sqrt (sr * σ * sr) with hQdef
  have hQPSD : Q.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hWW : Wᴴ * W = 1 := mul_eq_one_comm.1 hW
  have hFre : ((fidelity ρ σ : ℝ) : ℂ) = Q.trace := by
    have h0 : 0 ≤ Q.trace := hQPSD.trace_nonneg
    rw [Complex.nonneg_iff] at h0
    have hf : fidelity ρ σ = Q.trace.re := rfl
    rw [hf, Complex.ext_iff]
    exact ⟨rfl, by simpa using h0.2⟩
  refine ⟨sr, ss * Wᴴ, by rw [hsrH, hsrsr], ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hssH]
    calc ss * Wᴴ * (W * ss) = ss * (Wᴴ * W) * ss := by noncomm_ring
      _ = σ := by rw [hWW, Matrix.mul_one, hssss]
  · have h2 : (srᴴ * (ss * Wᴴ)).trace = Q.trace := by
      rw [hsrH]
      calc (sr * (ss * Wᴴ)).trace = (Q * W * Wᴴ).trace := by
            rw [show sr * (ss * Wᴴ) = (sr * ss) * Wᴴ by noncomm_ring, hMW]
        _ = (Q * (W * Wᴴ)).trace := by rw [Matrix.mul_assoc]
        _ = Q.trace := by rw [hW, Matrix.mul_one]
    rw [h2, ← hFre, Complex.norm_real, Real.norm_of_nonneg (fidelity_nonneg hσ)]

/-- **Uhlmann's theorem**, matrix form: the fidelity `Tr √(√ρ σ √ρ)` is the greatest
overlap `|Tr (Aᴴ B)|` over matrices `A`, `B` with `A Aᴴ = ρ` and `B Bᴴ = σ`. -/
theorem uhlmann_fidelity_matrix (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ A B : Matrix n n ℂ,
      A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ r = ‖(Aᴴ * B).trace‖} (fidelity ρ σ) := by
  constructor
  · exact exists_overlap_eq_fidelity hρ hσ
  · rintro r ⟨A, B, hA, hB, rfl⟩
    exact overlap_le_fidelity hρ hσ A B hA hB

/-- **Uhlmann's theorem**: the fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` of two positive
semidefinite states `ρ` and `σ` on `ℂ^n` is the maximal overlap `|⟪ψ, φ⟫|` over all
purifications `ψ` of `ρ` and `φ` of `σ` in `ℂ^n ⊗ ℂ^n`; a purification of `ρ` is a vector
whose reduced density matrix (partial trace over the second factor) is `ρ`. -/
theorem uhlmann_fidelity (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ ψ φ : n × n → ℂ,
      ptrace ψ = ρ ∧ ptrace φ = σ ∧ r = ‖∑ p, star (ψ p) * φ p‖} (fidelity ρ σ) := by
  constructor
  · obtain ⟨A, B, hA, hB, hval⟩ := exists_overlap_eq_fidelity hρ hσ
    refine ⟨fun p => A p.1 p.2, fun p => B p.1 p.2, ?_, ?_, ?_⟩
    · rw [ptrace_eq_mul_conjTranspose]
      exact hA
    · rw [ptrace_eq_mul_conjTranspose]
      exact hB
    · rw [overlap_eq_trace]
      exact hval
  · rintro r ⟨ψ, φ, hψ, hφ, rfl⟩
    rw [overlap_eq_trace]
    refine overlap_le_fidelity hρ hσ (toMat ψ) (toMat φ) ?_ ?_
    · rw [← ptrace_eq_mul_conjTranspose]; exact hψ
    · rw [← ptrace_eq_mul_conjTranspose]; exact hφ

end Main

end QI

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

