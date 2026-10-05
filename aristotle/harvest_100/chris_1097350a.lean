import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with finite-dimensional quantum systems, a state on `ℂⁿ` being described by a positive
semidefinite matrix `ρ : Matrix n n ℂ`.  Its fidelity with a second state `σ` is

`F(ρ, σ) = Tr √(√ρ σ √ρ)`,

which is `QI.fidelity`.

A *purification* of `ρ` in the doubled system `ℂⁿ ⊗ ℂⁿ` is a vector `u : n × n → ℂ` whose reduced
density matrix (partial trace over the second factor) is `ρ`; this is `QI.reducedDensity`.
`QI.uhlmann_fidelity` is Uhlmann's theorem: `F(ρ, σ)` is the *greatest* value of the overlap
`|⟪u, v⟫|` as `u` ranges over the purifications of `ρ` and `v` over those of `σ`.

The proof goes through the polar decomposition of a matrix (`QI.exists_unitary_polar`, proved
here from scratch by extending a linear isometry defined on a subspace) and the variational
characterisation of the trace norm (`QI.isGreatest_traceNorm`).
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

/-! ### An auxiliary extension lemma for linear isometries -/

/-- If `f g : E →ₗ[ℂ] E` satisfy `‖g x‖ = ‖f x‖` for all `x`, then there is a linear isometry `V`
of `E` with `V ∘ f = g`.  This is the key step in the polar decomposition. -/
theorem exists_linearIsometry_comp_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (f g : E →ₗ[ℂ] E) (h : ∀ x, ‖g x‖ = ‖f x‖) :
    ∃ V : E →ₗᵢ[ℂ] E, ∀ x, V (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx0 : ‖g x‖ = 0 := by rw [h x]; simp [LinearMap.mem_ker.mp hx]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp hx0
  set g' : (E ⧸ LinearMap.ker f) →ₗ[ℂ] E := (LinearMap.ker f).liftQ g hker with hg'
  set L₀ : (LinearMap.range f) →ₗ[ℂ] E := g'.comp (f.quotKerEquivRange.symm : _ →ₗ[ℂ] _) with hL₀
  have key : ∀ x : E, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hq : f.quotKerEquivRange (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ := rfl
    rw [hL₀]
    simp only [LinearMap.comp_apply, ← hq, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  have hnorm : ∀ y : LinearMap.range f, ‖L₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [key x]
    exact h x
  let L : (LinearMap.range f) →ₗᵢ[ℂ] E := ⟨L₀, hnorm⟩
  exact ⟨L.extend, fun x => (L.extend_apply ⟨f x, ⟨x, rfl⟩⟩).trans (key x)⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Polar decomposition -/

/-- **Polar decomposition** of a square complex matrix: every `M` can be written as
`√(M Mᴴ) * U` with `U` unitary. -/
theorem exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, M = CFC.sqrt (M * Mᴴ) * U := by
  set E := EuclideanSpace ℂ n
  set P := CFC.sqrt (M * Mᴴ) with hPdef
  have hMM : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  have hP : P.PosSemidef := (CFC.sqrt_nonneg (M * Mᴴ)).posSemidef
  have hPP : P * P = M * Mᴴ := CFC.sqrt_mul_sqrt_self _ (ha := hMM.nonneg)
  have hPh : Pᴴ = P := hP.isHermitian
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) with hT
  set p : E →L[ℂ] E := T P with hp
  set a : E →L[ℂ] E := T M with ha
  have hTM : T Mᴴ = star a := by rw [ha, ← map_star, Matrix.star_eq_conjTranspose]
  have hstar : star p * p = a * star a := by
    rw [hp, ha, ← map_star, ← map_star, ← map_mul, ← map_mul]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hPh, hPP]
  have hnormeq : ∀ x : E, ‖(star a) x‖ = ‖p x‖ := by
    intro x
    have h1 : ⟪(star p * p) x, x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have h2 : ⟪(a * star a) x, x⟫_ℂ = ⟪(star a) x, (star a) x⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply]
      have h := ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ) (star a) x ((star a) x)
      rw [ContinuousLinearMap.star_eq_adjoint] at h ⊢
      rwa [ContinuousLinearMap.adjoint_adjoint] at h
    have h3 : ⟪(star a) x, (star a) x⟫_ℂ = ⟪p x, p x⟫_ℂ := by rw [← h1, ← h2, hstar]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖(star a) x‖ ^ 2 = ‖p x‖ ^ 2 := by exact_mod_cast h3
    nlinarith [norm_nonneg ((star a) x), norm_nonneg (p x)]
  obtain ⟨V, hV⟩ := exists_linearIsometry_comp_eq (E := E) p.toLinearMap (star a).toLinearMap
    (by intro x; exact hnormeq x)
  simp only [ContinuousLinearMap.coe_coe] at hV
  set e : E ≃ₗᵢ[ℂ] E := V.toLinearIsometryEquiv rfl with he
  set u : E →L[ℂ] E := (e : E →L[ℂ] E) with hu
  have hue : ∀ x, u x = V x := fun x =>
    congrFun (LinearIsometry.coe_toLinearIsometryEquiv V rfl) x
  have huu : u ∈ unitary (E →L[ℂ] E) := by
    constructor
    · ext x; simp [hu, LinearIsometryEquiv.star_eq_symm]
    · ext x; simp [hu, LinearIsometryEquiv.star_eq_symm]
  have hup : u * p = star a := by
    ext x
    rw [ContinuousLinearMap.mul_apply, hue, hV x]
  set W : Matrix n n ℂ := T.symm u with hW
  have hWu : W ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', hW, ← map_star, ← map_mul, huu.1, map_one]
  have hWP : W * P = Mᴴ := by
    have h6 : W * P = T.symm (u * p) := by
      rw [map_mul, hW, hp, T.symm_apply_apply]
    rw [h6, hup, ← hTM, T.symm_apply_apply]
  refine ⟨Wᴴ, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hWu
  · have h7 := congrArg Matrix.conjTranspose hWP
    rw [Matrix.conjTranspose_mul, hPh, Matrix.conjTranspose_conjTranspose] at h7
    exact h7.symm

/-! ### Cauchy–Schwarz for the Frobenius inner product -/

omit [DecidableEq n] in
lemma trace_conjTranspose_mul (X Y : Matrix n n ℂ) :
    (Xᴴ * Y).trace = ∑ p : n × n, (starRingEnd ℂ) (X p.1 p.2) * Y p.1 p.2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, RCLike.star_def]
  exact Finset.sum_comm

omit [DecidableEq n] in
lemma norm_toLp_sq (X : Matrix n n ℂ) :
    ‖(WithLp.toLp 2 (fun p : n × n => X p.1 p.2) : EuclideanSpace ℂ (n × n))‖ ^ 2
      = (Xᴴ * X).trace.re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), trace_conjTranspose_mul,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  show ‖X p.1 p.2‖ ^ 2 = _
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

omit [DecidableEq n] in
lemma inner_toLp (X Y : Matrix n n ℂ) :
    ⟪(WithLp.toLp 2 (fun p : n × n => X p.1 p.2) : EuclideanSpace ℂ (n × n)),
      (WithLp.toLp 2 (fun p : n × n => Y p.1 p.2) : EuclideanSpace ℂ (n × n))⟫_ℂ
      = (Xᴴ * Y).trace := by
  rw [trace_conjTranspose_mul, PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

omit [DecidableEq n] in
/-- Cauchy–Schwarz inequality for the Frobenius (Hilbert–Schmidt) inner product on matrices. -/
theorem norm_trace_conjTranspose_mul_le (X Y : Matrix n n ℂ) :
    ‖(Xᴴ * Y).trace‖ ≤ Real.sqrt ((Xᴴ * X).trace.re) * Real.sqrt ((Yᴴ * Y).trace.re) := by
  rw [← inner_toLp, ← norm_toLp_sq, ← norm_toLp_sq,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm (𝕜 := ℂ) _ _

/-! ### The trace norm and its variational characterisation -/

/-- The trace norm (Schatten 1-norm) of a matrix: `‖M‖₁ = Tr √(M Mᴴ)`. -/
noncomputable def traceNorm (M : Matrix n n ℂ) : ℝ := (CFC.sqrt (M * Mᴴ)).trace.re

/-- The trace norm of `M` is the maximum of `‖Tr (W M)‖` over all unitaries `W`. -/
theorem isGreatest_traceNorm (M : Matrix n n ℂ) :
    IsGreatest {r : ℝ | ∃ W ∈ Matrix.unitaryGroup n ℂ, r = ‖(W * M).trace‖} (traceNorm M) := by
  set P := CFC.sqrt (M * Mᴴ) with hPdef
  obtain ⟨V, hV, hMV⟩ := exists_unitary_polar M
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hPh : Pᴴ = P := hP.isHermitian
  have htrnn : (0 : ℂ) ≤ P.trace := hP.trace_nonneg
  have htN : traceNorm M = P.trace.re := rfl
  have htr : P.trace = ((P.trace.re : ℝ) : ℂ) := Complex.eq_re_of_ofReal_le htrnn
  have htrre : 0 ≤ P.trace.re := (Complex.le_def.mp htrnn).1
  have hVV : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hV
  constructor
  · refine ⟨Vᴴ, by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hV, ?_⟩
    have hkey : (Vᴴ * M).trace = P.trace := by
      rw [hMV, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
    rw [hkey, htN, htr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htrre]
    exact Complex.ofReal_re _
  · rintro r ⟨W, hW, rfl⟩
    set S := CFC.sqrt P with hS
    have hSS : S * S = P := CFC.sqrt_mul_sqrt_self _ (ha := hP.nonneg)
    have hSh : Sᴴ = S := ((CFC.sqrt_nonneg P).posSemidef).isHermitian
    have hWW : Wᴴ * W = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hW
    have hXY : (S * Wᴴ)ᴴ * (S * V) = W * M := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.conjTranspose_conjTranspose, hMV,
        Matrix.mul_assoc, ← Matrix.mul_assoc S S V, hSS]
    have hXX : ((S * Wᴴ)ᴴ * (S * Wᴴ)).trace = P.trace := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc, ← Matrix.mul_assoc S S Wᴴ, hSS, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle, hWW, Matrix.one_mul]
    have hYY : ((S * V)ᴴ * (S * V)).trace = P.trace := by
      rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc, ← Matrix.mul_assoc S S V, hSS,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]
    calc ‖(W * M).trace‖ = ‖((S * Wᴴ)ᴴ * (S * V)).trace‖ := by rw [hXY]
      _ ≤ Real.sqrt (((S * Wᴴ)ᴴ * (S * Wᴴ)).trace.re) *
            Real.sqrt (((S * V)ᴴ * (S * V)).trace.re) :=
          norm_trace_conjTranspose_mul_le _ _
      _ = traceNorm M := by rw [hXX, hYY, htN]; exact Real.mul_self_sqrt htrre

/-! ### Fidelity -/

/-- The fidelity of two density matrices: `F(ρ, σ) = Tr √(√ρ σ √ρ)`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

lemma fidelity_eq_traceNorm {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    fidelity ρ σ = traceNorm (CFC.sqrt ρ * CFC.sqrt σ) := by
  have hRh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := ((CFC.sqrt_nonneg ρ).posSemidef).isHermitian
  have hSh : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := ((CFC.sqrt_nonneg σ).posSemidef).isHermitian
  have hSS : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self _ (ha := hσ.nonneg)
  have hmain : (CFC.sqrt ρ * CFC.sqrt σ) * (CFC.sqrt ρ * CFC.sqrt σ)ᴴ
      = CFC.sqrt ρ * σ * CFC.sqrt ρ := by
    rw [Matrix.conjTranspose_mul, hRh, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc (CFC.sqrt σ) (CFC.sqrt σ), hSS, ← Matrix.mul_assoc]
  rw [fidelity, traceNorm, hmain]

/-- **Uhlmann's theorem**, in matrix form.  Writing purifications of `ρ` and `σ` as matrices
`A`, `B` with `A Aᴴ = ρ` and `B Bᴴ = σ`, the fidelity is the greatest value of `|Tr (Aᴴ B)|`. -/
theorem uhlmann_fidelity_matrix {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ r = ‖(Aᴴ * B).trace‖}
      (fidelity ρ σ) := by
  have hRh : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := ((CFC.sqrt_nonneg ρ).posSemidef).isHermitian
  have hSh : (CFC.sqrt σ)ᴴ = CFC.sqrt σ := ((CFC.sqrt_nonneg σ).posSemidef).isHermitian
  have hRR : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self _ (ha := hρ.nonneg)
  have hSS : CFC.sqrt σ * CFC.sqrt σ = σ := CFC.sqrt_mul_sqrt_self _ (ha := hσ.nonneg)
  have hfid : fidelity ρ σ = traceNorm (CFC.sqrt ρ * CFC.sqrt σ) := fidelity_eq_traceNorm hσ
  obtain ⟨hmem, hub⟩ := isGreatest_traceNorm (CFC.sqrt ρ * CFC.sqrt σ)
  constructor
  · obtain ⟨W, hW, hWeq⟩ := hmem
    have hWWh : W * Wᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hW
    refine ⟨CFC.sqrt ρ, CFC.sqrt σ * W, by rw [hRh, hRR], ?_, ?_⟩
    · rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc,
        ← Matrix.mul_assoc W Wᴴ (CFC.sqrt σ), hWWh, Matrix.one_mul, hSS]
    · rw [hfid, hWeq, hRh, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  · rintro r ⟨A, B, hA, hB, rfl⟩
    obtain ⟨U₁, hU₁, hAU⟩ := exists_unitary_polar A
    obtain ⟨U₂, hU₂, hBU⟩ := exists_unitary_polar B
    rw [hA] at hAU
    rw [hB] at hBU
    have hkey : (Aᴴ * B).trace = ((U₂ * U₁ᴴ) * (CFC.sqrt ρ * CFC.sqrt σ)).trace := by
      rw [hAU, hBU, Matrix.conjTranspose_mul, hRh, Matrix.mul_assoc,
        ← Matrix.mul_assoc (CFC.sqrt ρ) (CFC.sqrt σ) U₂, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle]
    rw [hkey, hfid]
    refine hub ⟨U₂ * U₁ᴴ, Submonoid.mul_mem _ hU₂ ?_, rfl⟩
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU₁

/-! ### Purifications -/

/-- The overlap `⟪u, v⟫` of two bipartite pure states of `ℂⁿ ⊗ ℂⁿ`, written in coordinates. -/
noncomputable def overlap (u v : n × n → ℂ) : ℂ := ∑ p, (starRingEnd ℂ) (u p) * v p

/-- The reduced density matrix on the first factor of a bipartite pure state of `ℂⁿ ⊗ ℂⁿ`,
i.e. the partial trace of `|v⟩⟨v|` over the second factor. -/
noncomputable def reducedDensity (v : n × n → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, v (i, k) * (starRingEnd ℂ) (v (j, k))

/-- The matrix of coefficients of a bipartite pure state. -/
def curryMat (v : n × n → ℂ) : Matrix n n ℂ := Matrix.of fun i j => v (i, j)

omit [DecidableEq n] in
lemma reducedDensity_eq (v : n × n → ℂ) : reducedDensity v = curryMat v * (curryMat v)ᴴ := by
  ext i j
  simp [reducedDensity, curryMat, Matrix.mul_apply]

omit [DecidableEq n] in
lemma overlap_eq (u v : n × n → ℂ) : overlap u v = ((curryMat u)ᴴ * curryMat v).trace := by
  rw [trace_conjTranspose_mul]
  simp [overlap, curryMat]

omit [Fintype n] [DecidableEq n] in
lemma curryMat_uncurry (A : Matrix n n ℂ) : curryMat (fun p => A p.1 p.2) = A := rfl

/-- **Uhlmann's theorem.**  The fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` of two positive semidefinite
matrices is the greatest value of the overlap `|⟪u, v⟫|`, taken over all purifications `u` of `ρ`
and `v` of `σ` in `ℂⁿ ⊗ ℂⁿ`. -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {r : ℝ | ∃ u v : n × n → ℂ,
        reducedDensity u = ρ ∧ reducedDensity v = σ ∧ r = ‖overlap u v‖}
      (fidelity ρ σ) := by
  have hset : {r : ℝ | ∃ u v : n × n → ℂ,
        reducedDensity u = ρ ∧ reducedDensity v = σ ∧ r = ‖overlap u v‖}
      = {r : ℝ | ∃ A B : Matrix n n ℂ, A * Aᴴ = ρ ∧ B * Bᴴ = σ ∧ r = ‖(Aᴴ * B).trace‖} := by
    ext r
    constructor
    · rintro ⟨u, v, hu, hv, rfl⟩
      exact ⟨curryMat u, curryMat v, by rw [← reducedDensity_eq, hu],
        by rw [← reducedDensity_eq, hv], by rw [overlap_eq]⟩
    · rintro ⟨A, B, hA, hB, rfl⟩
      refine ⟨fun p => A p.1 p.2, fun p => B p.1 p.2, ?_, ?_, ?_⟩
      · rw [reducedDensity_eq, curryMat_uncurry, hA]
      · rw [reducedDensity_eq, curryMat_uncurry, hB]
      · rw [overlap_eq, curryMat_uncurry, curryMat_uncurry]
  rw [hset]
  exact uhlmann_fidelity_matrix hρ hσ

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

