/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Uhlmann's theorem

We work with finite-dimensional quantum systems, states being described by density
matrices (positive semidefinite matrices) on `ℂ^n`.

A *purification* of a state `ρ` on `ℂ^n` by an ancilla system `ℂ^m` is a vector
`ψ : n × m → ℂ` (i.e. an element of `ℂ^n ⊗ ℂ^m`) whose reduced state on the first
factor, `Tr_2 |ψ⟩⟨ψ|`, is `ρ`.

The *fidelity* of two states is `F(ρ, σ) = Tr √(√ρ σ √ρ)`.

Uhlmann's theorem states that `F(ρ, σ)` is the maximum of `|⟨ψ, ψ₂⟩|` over all
purifications `ψ` of `ρ` and `ψ₂` of `σ` (using an ancilla of the same dimension).
-/

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The partial trace over the second (ancilla) factor of `ℂ^n ⊗ ℂ^m`. -/
noncomputable def ptraceRight {m : Type*} [Fintype m] (X : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- The rank-one operator `|ψ⟩⟨ψ|` associated with a vector `ψ`. -/
def ketBra {N : Type*} (ψ : N → ℂ) : Matrix N N ℂ :=
  Matrix.of fun a b => ψ a * star (ψ b)

/-- `ψ : n × m → ℂ` is a purification of the state `ρ` on `ℂ^n` if the reduced density
matrix of `|ψ⟩⟨ψ|` on the first factor is `ρ`. -/
def IsPurification {m : Type*} [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) : Prop :=
  ptraceRight (ketBra ψ) = ρ

/-- The (Uhlmann) fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` of two states. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

section Aux

omit [DecidableEq n] in
/-- The dot product `x⋆ ⬝ y` is the inner product of the corresponding Euclidean vectors. -/
theorem dotProduct_eq_inner (u v : n → ℂ) :
    star u ⬝ᵥ v = inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ n) (WithLp.toLp 2 v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]

omit [DecidableEq n] in
/-- Cauchy-Schwarz: if `y` has the same norm as `x`, then `|⟨x, y⟩| ≤ ‖x‖²`. -/
theorem norm_dotProduct_le (x y : n → ℂ) (h : star y ⬝ᵥ y = star x ⬝ᵥ x) :
    ‖star x ⬝ᵥ y‖ ≤ (star x ⬝ᵥ x).re := by
  set X : EuclideanSpace ℂ n := WithLp.toLp 2 x
  set Y : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have hXX : (inner ℂ X X : ℂ).re = ‖X‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) X)
  have hYY : (inner ℂ Y Y : ℂ).re = ‖Y‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) Y)
  have h2 : ‖X‖ = ‖Y‖ := by
    have : ‖Y‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [← hXX, ← hYY, ← dotProduct_eq_inner, ← dotProduct_eq_inner, h]
    nlinarith [norm_nonneg X, norm_nonneg Y]
  rw [dotProduct_eq_inner x y, dotProduct_eq_inner x x, hXX]
  calc ‖(inner ℂ X Y : ℂ)‖ ≤ ‖X‖ * ‖Y‖ := norm_inner_le_norm _ _
    _ = ‖X‖ ^ 2 := by rw [← h2]; ring

/-- If `P` is positive semidefinite and `V` is an isometry then `‖Tr (V P)‖ ≤ Tr P`. -/
theorem norm_trace_mul_le_trace (P V : Matrix n n ℂ) (hP : P.PosSemidef) (hV : Vᴴ * V = 1) :
    ‖(V * P).trace‖ ≤ P.trace.re := by
  set S := CFC.sqrt P with hS
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg P).posSemidef.1
  have hconj : ∀ i k, star (S k i) = S i k := by
    intro i k
    have := congrFun (congrFun hSh i) k
    simpa [Matrix.conjTranspose_apply] using this
  have key : (V * P).trace = (S * V * S).trace := by
    rw [← hSS, ← Matrix.mul_assoc, Matrix.trace_mul_comm (V * S) S, Matrix.mul_assoc]
  set x : n → n → ℂ := fun i k => S k i with hx
  have hentry : ∀ i, (S * V * S) i i = star (x i) ⬝ᵥ (V *ᵥ x i) := by
    intro i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.star_apply, hx, hconj,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdiag : ∀ i, P i i = star (x i) ⬝ᵥ x i := by
    intro i
    rw [← hSS]
    simp only [Matrix.mul_apply, dotProduct, Pi.star_apply, hx, hconj]
  have hiso : ∀ i, star (V *ᵥ x i) ⬝ᵥ (V *ᵥ x i) = star (x i) ⬝ᵥ x i := by
    intro i
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hV, one_mulVec]
  calc ‖(V * P).trace‖ = ‖∑ i, (S * V * S) i i‖ := by rw [key, Matrix.trace]; rfl
    _ ≤ ∑ i, ‖(S * V * S) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (star (x i) ⬝ᵥ x i).re := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hentry i]
        exact norm_dotProduct_le _ _ (hiso i)
    _ = P.trace.re := by
        rw [Matrix.trace, Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← hdiag i]; rfl

omit [DecidableEq n] in
/-- Two square matrices agree as soon as they act identically on all vectors. -/
theorem matrix_ext_of_mulVec {A B : Matrix n n ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- `Matrix.toEuclideanLin` acts by matrix-vector multiplication. -/
theorem toEuclideanLin_apply_eq (M : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := rfl

/-- If `M` and `P` have the same "norm function", the assignment `P x ↦ M x` extends to a
linear isometry of the whole space. -/
theorem exists_isometry_of_norm_eq (P M : Matrix n n ℂ)
    (hnorm : ∀ x : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin M x‖ = ‖Matrix.toEuclideanLin P x‖) :
    ∃ F : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ n,
      ∀ x, F (Matrix.toEuclideanLin P x) = Matrix.toEuclideanLin M x := by
  set p := Matrix.toEuclideanLin P with hp
  set m := Matrix.toEuclideanLin M with hm
  have hker : LinearMap.ker p ≤ LinearMap.ker m := by
    intro x hx
    have : ‖m x‖ = 0 := by rw [hnorm x, LinearMap.mem_ker.1 hx, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.1 this
  set q := (LinearMap.ker p).liftQ m hker with hq
  set e := p.quotKerEquivRange with he
  set f₀ : (LinearMap.range p) →ₗ[ℂ] EuclideanSpace ℂ n := q ∘ₗ (e.symm : _ →ₗ[ℂ] _) with hf0
  have hf₀ : ∀ x, f₀ ⟨p x, ⟨x, rfl⟩⟩ = m x := by
    intro x
    have hex : e (Submodule.Quotient.mk x) = ⟨p x, ⟨x, rfl⟩⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk p x)
    have hsymm : e.symm ⟨p x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      rw [← hex, LinearEquiv.symm_apply_apply]
    simp [hf0, hsymm, hq]
  have hnorm₀ : ∀ y : LinearMap.range p, ‖f₀ y‖ = ‖(y : EuclideanSpace ℂ n)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hf₀ x]
    exact hnorm x
  refine ⟨LinearIsometry.extend ⟨f₀, hnorm₀⟩, fun x => ?_⟩
  have := LinearIsometry.extend_apply (⟨f₀, hnorm₀⟩ : (LinearMap.range p) →ₗᵢ[ℂ] EuclideanSpace ℂ n)
    ⟨p x, ⟨x, rfl⟩⟩
  simpa [hf₀ x] using this

/-- **Polar decomposition**: every square complex matrix `M` factors as `M = Q * √(Mᴴ M)`
with `Q` unitary. -/
theorem exists_polar (M : Matrix n n ℂ) :
    ∃ Q : Matrix n n ℂ, Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧ M = Q * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPS : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hPP : P * P = Mᴴ * M := CFC.sqrt_mul_sqrt_self _ hPS.nonneg
  have hPh : Pᴴ = P := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.1
  have hdot : ∀ x : n → ℂ, star (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
    intro x
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
      star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hPh, hPP]
  have hnorm : ∀ x : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin M x‖ = ‖Matrix.toEuclideanLin P x‖ := by
    intro x
    have h1 : ‖Matrix.toEuclideanLin M x‖ ^ 2 = ‖Matrix.toEuclideanLin P x‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (Matrix.toEuclideanLin M x),
        ← inner_self_eq_norm_sq (𝕜 := ℂ) (Matrix.toEuclideanLin P x),
        toEuclideanLin_apply_eq, toEuclideanLin_apply_eq,
        ← dotProduct_eq_inner, ← dotProduct_eq_inner, hdot]
    nlinarith [norm_nonneg (Matrix.toEuclideanLin M x), norm_nonneg (Matrix.toEuclideanLin P x)]
  obtain ⟨F, hF⟩ := exists_isometry_of_norm_eq P M hnorm
  set Q := Matrix.toEuclideanLin.symm F.toLinearMap with hQdef
  have hQvec : ∀ v : n → ℂ, Q *ᵥ v = WithLp.ofLp (F (WithLp.toLp 2 v)) := by
    intro v
    have hQe : Matrix.toEuclideanLin Q = F.toLinearMap := by
      rw [hQdef, LinearEquiv.apply_symm_apply]
    have := congrArg (fun (g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =>
      g (WithLp.toLp 2 v)) hQe
    simpa [toEuclideanLin_apply_eq] using congrArg WithLp.ofLp this
  have hQP : M = Q * P := by
    refine (matrix_ext_of_mulVec ?_).symm
    intro v
    rw [← Matrix.mulVec_mulVec, hQvec]
    have := hF (WithLp.toLp 2 v)
    simp only [toEuclideanLin_apply_eq] at this
    simpa using congrArg WithLp.ofLp this
  have hiso : Qᴴ * Q = 1 := by
    ext i j
    have h1 : star ((Pi.single i (1:ℂ) : n → ℂ)) ⬝ᵥ (Pi.single j (1:ℂ) : n → ℂ)
        = star (Q *ᵥ Pi.single i 1) ⬝ᵥ (Q *ᵥ Pi.single j 1) := by
      rw [dotProduct_eq_inner, dotProduct_eq_inner, hQvec, hQvec]
      simp
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def]
    rw [show ∑ k, (starRingEnd ℂ) (Q k i) * Q k j
          = star (Q *ᵥ (Pi.single i (1:ℂ) : n → ℂ)) ⬝ᵥ (Q *ᵥ (Pi.single j (1:ℂ) : n → ℂ)) by
        simp [dotProduct, Matrix.mulVec_single], ← h1]
    simp [dotProduct, Pi.single_apply, eq_comm]
  exact ⟨Q, hiso, mul_eq_one_comm.1 hiso, hQP⟩

/-- If `A * Aᴴ = ρ`, then `A = √ρ * U` for some unitary `U`. -/
theorem exists_unitary_of_mul_conjTranspose {A ρ : Matrix n n ℂ} (hA : A * Aᴴ = ρ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = CFC.sqrt ρ * U := by
  obtain ⟨Q, hQ1, hQ2, hQP⟩ := exists_polar Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, hA] at hQP
  refine ⟨Qᴴ, by simpa using hQ2, by simpa using hQ1, ?_⟩
  have := congrArg Matrix.conjTranspose hQP
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg ρ).posSemidef.1] at this

end Aux

section Bridge

omit [DecidableEq n] in
/-- The reduced density matrix of `|ψ⟩⟨ψ|`, written via the matricization of `ψ`. -/
theorem ptraceRight_ketBra (ψ : n × n → ℂ) :
    ptraceRight (ketBra ψ) = (Matrix.of fun i k => ψ (i, k)) * (Matrix.of fun i k => ψ (i, k))ᴴ := by
  ext i j
  simp [ptraceRight, ketBra, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
/-- The overlap of two vectors, written via their matricizations. -/
theorem overlap_eq_trace (ψ ψ₂ : n × n → ℂ) :
    ∑ a, star (ψ a) * ψ₂ a =
      ((Matrix.of fun i k => ψ (i, k))ᴴ * (Matrix.of fun i k => ψ₂ (i, k))).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

end Bridge

/-- **Uhlmann's theorem.** For states (positive semidefinite matrices) `ρ` and `σ` on `ℂ^n`,
the fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` is the maximum of the overlap `|⟨ψ, ψ₂⟩|` taken over
all purifications `ψ` of `ρ` and `ψ₂` of `σ` in `ℂ^n ⊗ ℂ^n`. -/
theorem uhlmann_fidelity {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ ψ₂ : n × n → ℂ, IsPurification ρ ψ ∧ IsPurification σ ψ₂ ∧
      x = ‖∑ a, star (ψ a) * ψ₂ a‖} (fidelity ρ σ) := by
  set R := CFC.sqrt ρ with hRdef
  set T := CFC.sqrt σ with hTdef
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self _ hρ.nonneg
  have hTT : T * T = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  have hRh : Rᴴ = R := (CFC.sqrt_nonneg ρ).posSemidef.1
  have hTh : Tᴴ = T := (CFC.sqrt_nonneg σ).posSemidef.1
  set M := T * R with hMdef
  have hMh : Mᴴ = R * T := by rw [hMdef, Matrix.conjTranspose_mul, hRh, hTh]
  have hMM : Mᴴ * M = R * σ * R := by
    rw [hMh, hMdef, ← hTT]
    simp [Matrix.mul_assoc]
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hPS : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hfid : fidelity ρ σ = P.trace.re := by rw [fidelity, hPdef, hMM]
  obtain ⟨Q, hQ1, hQ2, hQP⟩ := exists_polar M
  have hMhP : Mᴴ = P * Qᴴ := by
    rw [hQP, Matrix.conjTranspose_mul, ← hPdef, (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef.1]
  constructor
  · -- the maximum is attained, by the purifications `√ρ` and `√σ Q`
    refine ⟨fun a => R a.1 a.2, fun a => (T * Q) a.1 a.2, ?_, ?_, ?_⟩
    · show ptraceRight (ketBra _) = ρ
      rw [ptraceRight_ketBra]
      show R * Rᴴ = ρ
      rw [hRh, hRR]
    · show ptraceRight (ketBra _) = σ
      rw [ptraceRight_ketBra]
      show T * Q * (T * Q)ᴴ = σ
      rw [Matrix.conjTranspose_mul, hTh, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ2,
        Matrix.one_mul, hTT]
    · rw [overlap_eq_trace]
      show _ = ‖(Rᴴ * (T * Q)).trace‖
      rw [hRh, ← Matrix.mul_assoc, ← hMh, hMhP, Matrix.mul_assoc, hQ1, Matrix.mul_one, hfid]
      exact Complex.re_eq_norm.mpr hPS.trace_nonneg
  · -- every overlap of purifications is bounded by the fidelity
    rintro x ⟨ψ, ψ₂, hψ, hψ₂, rfl⟩
    rw [IsPurification, ptraceRight_ketBra] at hψ hψ₂
    obtain ⟨U, hU1, hU2, hAU⟩ := exists_unitary_of_mul_conjTranspose hψ
    obtain ⟨V, hV1, hV2, hBV⟩ := exists_unitary_of_mul_conjTranspose hψ₂
    rw [overlap_eq_trace, hAU, hBV, hfid]
    have hW : (V * Uᴴ)ᴴ * (V * Uᴴ) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Vᴴ, hV1, Matrix.one_mul, hU2]
    have hiso : (Qᴴ * (V * Uᴴ))ᴴ * (Qᴴ * (V * Uᴴ)) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc Q, hQ2, Matrix.one_mul, hW]
    have hkey : ((R * U)ᴴ * (T * V)).trace = (Qᴴ * (V * Uᴴ) * P).trace := by
      rw [Matrix.conjTranspose_mul, hRh]
      calc (Uᴴ * R * (T * V)).trace = (Uᴴ * (R * T * V)).trace := by simp [Matrix.mul_assoc]
        _ = (R * T * V * Uᴴ).trace := Matrix.trace_mul_comm _ _
        _ = (R * T * (V * Uᴴ)).trace := by simp [Matrix.mul_assoc]
        _ = (Mᴴ * (V * Uᴴ)).trace := by rw [hMh]
        _ = (P * (Qᴴ * (V * Uᴴ))).trace := by rw [hMhP]; simp [Matrix.mul_assoc]
        _ = (Qᴴ * (V * Uᴴ) * P).trace := Matrix.trace_mul_comm _ _
    rw [hkey]
    exact norm_trace_mul_le_trace P _ hPS hiso

end QI

