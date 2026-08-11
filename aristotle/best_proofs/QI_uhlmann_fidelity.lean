import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Isometries defined on the range of a linear map -/

section Isom

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- If `f` and `g` have the same norm pointwise, there is a linear isometry defined on the
range of `f` sending `f x` to `g x`. -/
theorem exists_isometry_on_range (f : E →ₗ[ℂ] F) (g : E →ₗ[ℂ] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ L : (LinearMap.range f) →ₗᵢ[ℂ] G,
      ∀ x : E, L ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx' : f x = 0 := hx
    have hnx := h x
    rw [hx'] at hnx
    simp at hnx
    simpa [LinearMap.mem_ker] using hnx.symm
  set q : (E ⧸ LinearMap.ker f) →ₗ[ℂ] G := (LinearMap.ker f).liftQ g hker with hq
  set e : (E ⧸ LinearMap.ker f) ≃ₗ[ℂ] (LinearMap.range f) := f.quotKerEquivRange with he
  set L₀ : (LinearMap.range f) →ₗ[ℂ] G := q ∘ₗ (e.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀
  have key : ∀ x : E, L₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have hx : e (Submodule.Quotient.mk x) = ⟨f x, LinearMap.mem_range_self f x⟩ := by
      apply Subtype.ext
      rw [he]
      exact f.quotKerEquivRange_apply_mk x
    rw [hL₀]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← hx,
      LinearEquiv.symm_apply_apply, hq, Submodule.liftQ_apply]
  refine ⟨⟨L₀, ?_⟩, key⟩
  rintro ⟨s, x, rfl⟩
  rw [key x]
  simpa using (h x).symm

/-- A norm-preserving pair of maps yields a contraction `T : F →ₗ G` with `T (f x) = g x`. -/
theorem exists_contraction_extension [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) (g : E →ₗ[ℂ] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ T : F →ₗ[ℂ] G, (∀ x, T (f x) = g x) ∧ ∀ y, ‖T y‖ ≤ ‖y‖ := by
  obtain ⟨L, hL⟩ := exists_isometry_on_range f g h
  refine ⟨L.toLinearMap ∘ₗ ((LinearMap.range f).orthogonalProjection : F →ₗ[ℂ] _), ?_, ?_⟩
  · intro x
    have hx : (LinearMap.range f).orthogonalProjection (f x)
        = ⟨f x, LinearMap.mem_range_self f x⟩ := by
      apply Subtype.ext
      simpa using Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self f x)
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, hx, hL x]
  · intro y
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]
    exact Submodule.norm_orthogonalProjection_apply_le _ y

/-- A norm-preserving pair of endomorphisms of a finite dimensional space is intertwined by a
global linear isometry. -/
theorem exists_isometry_extension [FiniteDimensional ℂ E] (f g : E →ₗ[ℂ] E)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : E →ₗᵢ[ℂ] E, ∀ x, U (f x) = g x := by
  obtain ⟨L, hL⟩ := exists_isometry_on_range f g h
  refine ⟨L.extend, fun x => ?_⟩
  have hx := L.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩
  simpa [hL x] using hx

end Isom

/-! ### Euclidean vectors and the Frobenius (Hilbert–Schmidt) inner product -/

variable {n m k : Type} [Fintype n] [Fintype m] [Fintype k]

/-- A plain function viewed as a vector of `EuclideanSpace`. -/
noncomputable def evec (x : n → ℂ) : EuclideanSpace ℂ n := WithLp.toLp 2 x

theorem inner_evec (x y : n → ℂ) : inner ℂ (evec x) (evec y) = star x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [evec, dotProduct_comm]

theorem normSq_evec (x : n → ℂ) : ‖evec x‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h : (‖evec x‖ ^ 2 : ℝ) = ∑ i, ‖x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rfl
  rw [h, dotProduct]
  simp [Complex.re_sum, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

theorem dot_conjTranspose (M : Matrix n m ℂ) (y : m → ℂ) (z : n → ℂ) :
    star (M *ᵥ y) ⬝ᵥ z = star y ⬝ᵥ (Mᴴ *ᵥ z) := by
  rw [Matrix.star_mulVec, dotProduct_mulVec]

theorem normSq_mulVec (M : Matrix n m ℂ) (x : m → ℂ) :
    ‖evec (M *ᵥ x)‖ ^ 2 = (star x ⬝ᵥ ((Mᴴ * M) *ᵥ x)).re := by
  rw [normSq_evec, dot_conjTranspose, ← Matrix.mulVec_mulVec]

/-- Two matrices with the same `Mᴴ M` act with the same norm on every vector. -/
theorem norm_mulVec_congr {M : Matrix n m ℂ} {P : Matrix k m ℂ} (h : Mᴴ * M = Pᴴ * P)
    (x : m → ℂ) : ‖evec (M *ᵥ x)‖ = ‖evec (P *ᵥ x)‖ := by
  have h2 : ‖evec (M *ᵥ x)‖ ^ 2 = ‖evec (P *ᵥ x)‖ ^ 2 := by
    rw [normSq_mulVec, normSq_mulVec, h]
  nlinarith [norm_nonneg (evec (M *ᵥ x)), norm_nonneg (evec (P *ᵥ x))]

/-- A matrix viewed as a vector of `EuclideanSpace` indexed by pairs; its norm is the
Frobenius (Hilbert–Schmidt) norm. -/
noncomputable def fro (X : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

theorem inner_fro (X Y : Matrix n m ℂ) : inner ℂ (fro X) (fro Y) = (Xᴴ * Y).trace := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [fro, dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    mul_comm]
  rw [Finset.sum_comm]

theorem normSq_fro (X : Matrix n m ℂ) : ((‖fro X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
  rw [← inner_fro X X, EuclideanSpace.inner_eq_star_dotProduct]
  have h : (‖fro X‖ ^ 2 : ℝ) = ∑ p : n × m, ‖X p.1 p.2‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    rfl
  rw [h]
  push_cast
  simp [fro, dotProduct, ← Complex.mul_conj']

/-- Cauchy–Schwarz for the Frobenius inner product. -/
theorem norm_trace_le (X Y : Matrix n m ℂ) : ‖(Xᴴ * Y).trace‖ ≤ ‖fro X‖ * ‖fro Y‖ := by
  rw [← inner_fro X Y]
  exact norm_inner_le_norm _ _

/-- The Frobenius norm expressed columnwise. -/
theorem normSq_fro_eq_sum_col (X : Matrix n m ℂ) :
    ‖fro X‖ ^ 2 = ∑ j, ‖evec (fun i => X i j)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

/-! ### Contractions -/

/-- `M` is a contraction: it does not increase the Euclidean norm. -/
def IsContr (M : Matrix n m ℂ) : Prop := ∀ x : m → ℂ, ‖evec (M *ᵥ x)‖ ≤ ‖evec x‖

theorem IsContr.mul {A : Matrix n m ℂ} {B : Matrix m k ℂ} (hA : IsContr A) (hB : IsContr B) :
    IsContr (A * B) := by
  intro x
  rw [← Matrix.mulVec_mulVec]
  exact (hA _).trans (hB x)

/-- If `Mᴴ` is a contraction then so is `M`. -/
theorem IsContr.of_conjTranspose {M : Matrix n m ℂ} (h : IsContr Mᴴ) : IsContr M := by
  intro y
  have key : ‖evec (M *ᵥ y)‖ ^ 2 ≤ ‖evec y‖ * ‖evec (M *ᵥ y)‖ := by
    have h1 : (‖evec (M *ᵥ y)‖ ^ 2 : ℝ) = ‖inner ℂ (evec y) (evec (Mᴴ *ᵥ (M *ᵥ y)))‖ := by
      rw [inner_evec, ← dot_conjTranspose, ← inner_evec, inner_self_eq_norm_sq_to_K]
      simp
    rw [h1]
    calc ‖inner ℂ (evec y) (evec (Mᴴ *ᵥ (M *ᵥ y)))‖
        ≤ ‖evec y‖ * ‖evec (Mᴴ *ᵥ (M *ᵥ y))‖ := norm_inner_le_norm _ _
      _ ≤ ‖evec y‖ * ‖evec (M *ᵥ y)‖ :=
          mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg (evec (M *ᵥ y))) with he | hp
  · rw [← he]; exact norm_nonneg _
  · nlinarith

theorem IsContr.of_isUnitary [DecidableEq n] {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) : IsContr U := by
  intro x
  have h : ‖evec (U *ᵥ x)‖ ^ 2 = ‖evec x‖ ^ 2 := by
    rw [normSq_mulVec, hU, Matrix.one_mulVec, normSq_evec]
  nlinarith [norm_nonneg (evec (U *ᵥ x)), norm_nonneg (evec x)]

theorem IsContr.fro_mul {Z : Matrix n n ℂ} (hZ : IsContr Z) (X : Matrix n m ℂ) :
    ‖fro (Z * X)‖ ≤ ‖fro X‖ := by
  have hcol : ∀ j : m, (fun i => (Z * X) i j) = Z *ᵥ (fun i => X i j) := by
    intro j
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hsq : ‖fro (Z * X)‖ ^ 2 ≤ ‖fro X‖ ^ 2 := by
    rw [normSq_fro_eq_sum_col, normSq_fro_eq_sum_col]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hcol j]
    have h1 := hZ (fun i => X i j)
    nlinarith [norm_nonneg (evec (Z *ᵥ fun i => X i j)), norm_nonneg (evec fun i => X i j)]
  nlinarith [norm_nonneg (fro (Z * X)), norm_nonneg (fro X)]

/-! ### Polar decomposition and factorization of matrices -/

omit [Fintype n] in
theorem evec_injective : Function.Injective (evec : (n → ℂ) → EuclideanSpace ℂ n) :=
  fun _ _ h => congrArg WithLp.ofLp h

/-- A matrix preserving the inner product is unitary. -/
theorem isUnitary_of_inner [DecidableEq n] {U : Matrix n n ℂ}
    (h : ∀ x y : n → ℂ, star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = star x ⬝ᵥ y) : Uᴴ * U = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  funext i
  have h1 := h (Pi.single i 1) y
  rw [dot_conjTranspose, Matrix.mulVec_mulVec] at h1
  simpa using h1

/-- Polar decomposition: every square matrix `M` factors as `U * √(Mᴴ M)` with `U` unitary. -/
theorem exists_polar [DecidableEq n] (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ M = U * CFC.sqrt (Mᴴ * M) := by
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have h0 : (0 : Matrix n n ℂ) ≤ Mᴴ * M := (posSemidef_conjTranspose_mul_self M).nonneg
  have hPherm : Pᴴ = P := ((CFC.sqrt_nonneg (Mᴴ * M)).posSemidef).isHermitian
  have hPP : Mᴴ * M = Pᴴ * P := by rw [hPherm, hPdef, CFC.sqrt_mul_sqrt_self (Mᴴ * M)]
  have hnorm : ∀ v : EuclideanSpace ℂ n,
      ‖(Matrix.toEuclideanLin P) v‖ = ‖(Matrix.toEuclideanLin M) v‖ :=
    fun v => (norm_mulVec_congr hPP v.ofLp).symm
  obtain ⟨U₀, hU₀⟩ :=
    exists_isometry_extension (Matrix.toEuclideanLin P) (Matrix.toEuclideanLin M) hnorm
  set U := Matrix.toEuclideanLin.symm U₀.toLinearMap with hUdef
  have hlin : Matrix.toEuclideanLin U = U₀.toLinearMap := by
    rw [hUdef, LinearEquiv.apply_symm_apply]
  have hUapply : ∀ x : n → ℂ, evec (U *ᵥ x) = U₀ (evec x) := by
    intro x
    have : Matrix.toEuclideanLin U (evec x) = U₀.toLinearMap (evec x) := by rw [hlin]
    exact this
  refine ⟨U, ?_, ?_⟩
  · refine isUnitary_of_inner fun x y => ?_
    rw [← inner_evec, hUapply, hUapply, U₀.inner_map_map, inner_evec]
  · rw [Matrix.ext_iff_mulVec]
    intro y
    refine evec_injective ?_
    rw [← Matrix.mulVec_mulVec, hUapply]
    have h1 : evec (P *ᵥ y) = Matrix.toEuclideanLin P (evec y) := rfl
    rw [h1, hU₀ (evec y)]
    rfl

/-- If `A Aᴴ = C Cᴴ` then `A = C V` for some `V` with `Vᴴ` a contraction. -/
theorem exists_factor [DecidableEq n] [DecidableEq k] {A : Matrix n m ℂ} {C : Matrix n k ℂ}
    (h : A * Aᴴ = C * Cᴴ) :
    ∃ V : Matrix k m ℂ, A = C * V ∧ IsContr Vᴴ := by
  have hCA : (Cᴴ)ᴴ * Cᴴ = (Aᴴ)ᴴ * Aᴴ := by
    simp only [Matrix.conjTranspose_conjTranspose]
    exact h.symm
  have hnorm : ∀ v : EuclideanSpace ℂ n,
      ‖(Matrix.toEuclideanLin Cᴴ) v‖ = ‖(Matrix.toEuclideanLin Aᴴ) v‖ :=
    fun v => norm_mulVec_congr hCA v.ofLp
  obtain ⟨T, hT, hTc⟩ :=
    exists_contraction_extension (Matrix.toEuclideanLin Cᴴ) (Matrix.toEuclideanLin Aᴴ) hnorm
  set W := Matrix.toEuclideanLin.symm T with hWdef
  have hlin : Matrix.toEuclideanLin W = T := by rw [hWdef, LinearEquiv.apply_symm_apply]
  have hWapply : ∀ z : k → ℂ, evec (W *ᵥ z) = T (evec z) := by
    intro z
    have : Matrix.toEuclideanLin W (evec z) = T (evec z) := by rw [hlin]
    exact this
  refine ⟨Wᴴ, ?_, ?_⟩
  · have hAW : Aᴴ = W * Cᴴ := by
      rw [Matrix.ext_iff_mulVec]
      intro x
      refine evec_injective ?_
      rw [← Matrix.mulVec_mulVec, hWapply]
      have h1 : evec (Cᴴ *ᵥ x) = Matrix.toEuclideanLin Cᴴ (evec x) := rfl
      rw [h1, hT (evec x)]
      rfl
    have := congrArg Matrix.conjTranspose hAW
    simpa using this
  · intro z
    rw [Matrix.conjTranspose_conjTranspose, hWapply z]
    exact hTc _

/-- Trace-norm duality bound: `|tr (Nᴴ W)| ≤ tr √(Nᴴ N)` for any contraction `W`. -/
theorem norm_trace_conjTranspose_mul_le [DecidableEq n] {N W : Matrix n n ℂ} (hW : IsContr W) :
    ‖(Nᴴ * W).trace‖ ≤ (Matrix.trace (CFC.sqrt (Nᴴ * N))).re := by
  obtain ⟨U, hU, hNU⟩ := exists_polar N
  set P := CFC.sqrt (Nᴴ * N) with hPdef
  have hPnn : (0 : Matrix n n ℂ) ≤ P := CFC.sqrt_nonneg _
  have hPherm : Pᴴ = P := hPnn.posSemidef.isHermitian
  set Q := CFC.sqrt P with hQdef
  have hQnn : (0 : Matrix n n ℂ) ≤ Q := CFC.sqrt_nonneg _
  have hQherm : Qᴴ = Q := hQnn.posSemidef.isHermitian
  have hQQ : Q * Q = P := CFC.sqrt_mul_sqrt_self P
  have hNH : Nᴴ = P * Uᴴ := by
    rw [hNU, Matrix.conjTranspose_mul, hPherm]
  -- `Z` is a contraction
  have hUc : IsContr Uᴴ := by
    refine IsContr.of_isUnitary ?_
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have hZ : IsContr (Uᴴ * W) := hUc.mul hW
  have etr : (Nᴴ * W).trace = (Qᴴ * ((Uᴴ * W) * Q)).trace := by
    calc (Nᴴ * W).trace = ((Q * Q) * (Uᴴ * W)).trace := by
          rw [hNH, hQQ, mul_assoc]
      _ = ((Uᴴ * W) * (Q * Q)).trace := Matrix.trace_mul_comm _ _
      _ = (((Uᴴ * W) * Q) * Q).trace := by rw [mul_assoc (Uᴴ * W) Q Q]
      _ = (Q * ((Uᴴ * W) * Q)).trace := Matrix.trace_mul_comm _ _
      _ = (Qᴴ * ((Uᴴ * W) * Q)).trace := by rw [hQherm]
  have hfro : ((‖fro Q‖ ^ 2 : ℝ) : ℂ) = P.trace := by
    rw [normSq_fro, hQherm, hQQ]
  have hfro' : (‖fro Q‖ ^ 2 : ℝ) = P.trace.re := by
    rw [← Complex.ofReal_re (‖fro Q‖ ^ 2), hfro]
  rw [etr]
  calc ‖(Qᴴ * ((Uᴴ * W) * Q)).trace‖ ≤ ‖fro Q‖ * ‖fro ((Uᴴ * W) * Q)‖ := norm_trace_le _ _
    _ ≤ ‖fro Q‖ * ‖fro Q‖ := by
        exact mul_le_mul_of_nonneg_left (hZ.fro_mul Q) (norm_nonneg _)
    _ = P.trace.re := by rw [← hfro']; ring

/-! ### Fidelity and purifications -/

/-- The reduced density matrix of a pure state `psi` of a bipartite system `H_n ⊗ H_m`,
whose coefficients are recorded as the matrix `psi`: the partial trace over the ancilla,
`(reducedState psi) i j = ∑ k, psi i k * conj (psi j k)`. -/
noncomputable def reducedState (psi : Matrix n m ℂ) : Matrix n n ℂ := psi * psiᴴ

/-- The inner product of two pure states of the bipartite system `H_n ⊗ H_m`:
`overlap psi phi = ∑ i k, conj (psi i k) * phi i k`. -/
noncomputable def overlap (psi phi : Matrix n m ℂ) : ℂ := (psiᴴ * phi).trace

omit [Fintype n] in
theorem reducedState_apply (psi : Matrix n m ℂ) (i j : n) :
    reducedState psi i j = ∑ l, psi i l * (starRingEnd ℂ) (psi j l) := by
  simp [reducedState, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem overlap_eq_sum (psi phi : Matrix n m ℂ) :
    overlap psi phi = ∑ i, ∑ l, (starRingEnd ℂ) (psi i l) * phi i l := by
  rw [overlap, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- The fidelity `F (ρ, σ) = tr √(√ρ σ √ρ)` of two density matrices. -/
noncomputable def fidelity [DecidableEq n] (rho sigma : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt rho * sigma * CFC.sqrt rho))).re

/-- **Uhlmann's theorem**: the fidelity of two positive semidefinite matrices (density
matrices) is the maximum, over all purifications `psi` of `rho` and `phi` of `sigma` with an
arbitrary finite ancilla, of the modulus of their overlap. -/
theorem uhlmann_fidelity [DecidableEq n] {rho sigma : Matrix n n ℂ}
    (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    IsGreatest {x : ℝ | ∃ (m : Type) (fm : Fintype m) (psi phi : Matrix n m ℂ),
        letI := fm
        reducedState psi = rho ∧ reducedState phi = sigma ∧ x = ‖overlap psi phi‖}
      (fidelity rho sigma) := by
  set R := CFC.sqrt rho with hRdef
  set S := CFC.sqrt sigma with hSdef
  have hRherm : Rᴴ = R := (CFC.sqrt_nonneg rho).posSemidef.isHermitian
  have hSherm : Sᴴ = S := (CFC.sqrt_nonneg sigma).posSemidef.isHermitian
  have hRR : R * R = rho := CFC.sqrt_mul_sqrt_self (ha := hrho.nonneg) rho
  have hSS : S * S = sigma := CFC.sqrt_mul_sqrt_self (ha := hsigma.nonneg) sigma
  set N := S * R with hNdef
  have hNH : Nᴴ = R * S := by rw [hNdef, Matrix.conjTranspose_mul, hRherm, hSherm]
  have hNN : Nᴴ * N = R * sigma * R := by
    rw [hNH, hNdef, mul_assoc, ← mul_assoc S S R, hSS, ← mul_assoc]
  have hfid : fidelity rho sigma = (Matrix.trace (CFC.sqrt (Nᴴ * N))).re := by
    rw [fidelity, hNN]
  set P := CFC.sqrt (Nᴴ * N) with hPdef
  have hPherm : Pᴴ = P := (CFC.sqrt_nonneg (Nᴴ * N)).posSemidef.isHermitian
  constructor
  · -- the fidelity is attained by an explicit pair of purifications
    obtain ⟨U, hU, hNU⟩ := exists_polar N
    have hUUh : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
    refine ⟨n, inferInstance, R, S * U, ?_, ?_, ?_⟩
    · rw [reducedState, hRherm, hRR]
    · rw [reducedState, Matrix.conjTranspose_mul, hSherm]
      calc S * U * (Uᴴ * S) = S * (U * Uᴴ) * S := by
            simp only [mul_assoc]
        _ = sigma := by rw [hUUh, mul_one, hSS]
    · have hNH2 : Nᴴ = P * Uᴴ := by rw [hNU, Matrix.conjTranspose_mul, hPherm]
      have hov : overlap R (S * U) = Matrix.trace P := by
        rw [overlap, hRherm]
        calc (R * (S * U)).trace = (Nᴴ * U).trace := by rw [hNH, mul_assoc]
          _ = (P * (Uᴴ * U)).trace := by rw [hNH2, mul_assoc]
          _ = Matrix.trace P := by rw [hU, mul_one]
      rw [hov, hfid]
      exact (Complex.re_eq_norm.mpr (CFC.sqrt_nonneg (Nᴴ * N)).posSemidef.trace_nonneg)
  · -- every pair of purifications has overlap at most the fidelity
    rintro x ⟨m', fm, psi, phi, hpsi, hphi, rfl⟩
    obtain ⟨VA, hVA, hVAc⟩ : ∃ V : Matrix n m' ℂ, psi = R * V ∧ IsContr Vᴴ := by
      refine exists_factor ?_
      rw [hRherm, hRR, ← hpsi, reducedState]
    obtain ⟨VB, hVB, hVBc⟩ : ∃ V : Matrix n m' ℂ, phi = S * V ∧ IsContr Vᴴ := by
      refine exists_factor ?_
      rw [hSherm, hSS, ← hphi, reducedState]
    have hW : IsContr (VB * VAᴴ) := (IsContr.of_conjTranspose hVBc).mul hVAc
    have hov : overlap psi phi = (Nᴴ * (VB * VAᴴ)).trace := by
      rw [overlap, hVA, hVB, Matrix.conjTranspose_mul, hRherm, hNH]
      calc (VAᴴ * R * (S * VB)).trace = (VAᴴ * (R * S * VB)).trace := by
            simp only [Matrix.mul_assoc]
        _ = ((R * S * VB) * VAᴴ).trace := Matrix.trace_mul_comm _ _
        _ = (R * S * (VB * VAᴴ)).trace := by simp only [Matrix.mul_assoc]
    rw [hov, hfid]
    exact norm_trace_conjTranspose_mul_le hW

end QI

