import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m]
  [Fintype d] [DecidableEq d]

/-- The real quadratic form associated with a matrix `Q`: `x ↦ Re (xᴴ Q x)`. -/
noncomputable def qform (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ Q *ᵥ x)

/-- `Q` is positive definite on the subspace `S`. -/
def PosDefOn (Q : Matrix m m 𝕜) (S : Submodule 𝕜 (m → 𝕜)) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < qform Q x

/-- The positive index of inertia of a Hermitian matrix: the number of positive
eigenvalues (and `0` for non-Hermitian matrices). -/
noncomputable def posIndex (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then
    {i : m | 0 < h.eigenvalues i}.toFinset.card
  else 0

lemma posIndex_of_isHermitian {Q : Matrix m m 𝕜} (h : Q.IsHermitian) :
    posIndex Q = {i : m | 0 < h.eigenvalues i}.toFinset.card := by
  rw [posIndex, dif_pos h]

omit [DecidableEq m] in
@[simp] lemma qform_zero (Q : Matrix m m 𝕜) : qform Q 0 = 0 := by
  simp [qform]

omit [DecidableEq m] [DecidableEq d] in
/-- Compression identity for the quadratic form. -/
lemma qform_compression (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜) (y : d → 𝕜) :
    qform Q (B *ᵥ y) = qform (Bᴴ * Q * B) y := by
  unfold qform
  congr 1
  rw [star_mulVec, mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul,
    ← dotProduct_mulVec, mulVec_mulVec]

/-- The coordinate subspace supported on a finite set `s`. -/
noncomputable def coordSpace (s : Finset m) : Submodule 𝕜 (m → 𝕜) :=
  Submodule.span 𝕜 (Set.range (fun i : s => (Pi.single (i : m) (1 : 𝕜) : m → 𝕜)))

lemma finrank_coordSpace (s : Finset m) :
    Module.finrank 𝕜 (coordSpace (𝕜 := 𝕜) s) = s.card := by
  have hli : LinearIndependent 𝕜 (fun i : s => (Pi.single (i : m) (1 : 𝕜) : m → 𝕜)) := by
    have h := (Pi.basisFun 𝕜 m).linearIndependent
    have h2 := h.comp (fun i : s => (i : m)) Subtype.val_injective
    simpa [Function.comp_def] using h2
  rw [coordSpace, finrank_span_eq_card hli]
  simp

omit [Fintype m] in
lemma coordSpace_apply_eq_zero {s : Finset m} {y : m → 𝕜} (hy : y ∈ coordSpace (𝕜 := 𝕜) s)
    {j : m} (hj : j ∉ s) : y j = 0 := by
  have hle : coordSpace (𝕜 := 𝕜) s ≤ LinearMap.ker (LinearMap.proj j : (m → 𝕜) →ₗ[𝕜] 𝕜) := by
    rw [coordSpace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hij : (i : m) ≠ j := fun h => hj (h ▸ i.2)
    simp [LinearMap.mem_ker, hij]
  exact hle hy

/-- The quadratic form of a diagonal matrix. -/
lemma qform_diagonal (lam : m → ℝ) (y : m → 𝕜) :
    qform (diagonal (RCLike.ofReal ∘ lam : m → 𝕜)) y = ∑ i, lam i * ‖y i‖ ^ 2 := by
  unfold qform
  simp only [dotProduct, mulVec_diagonal, map_sum, Pi.star_apply, RCLike.star_def,
    Function.comp_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, mul_comm (starRingEnd 𝕜 (y x)), mul_assoc, RCLike.conj_mul]
  simp

lemma conj_eigenvectorUnitary (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * Q * (hQ.eigenvectorUnitary : Matrix m m 𝕜)
      = diagonal (RCLike.ofReal ∘ hQ.eigenvalues) := by
  have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  simpa using h

/-- Diagonalisation of the quadratic form in eigen-coordinates. -/
lemma qform_eigen (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) (y : m → 𝕜) :
    qform Q ((hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ y) =
      ∑ i, hQ.eigenvalues i * ‖y i‖ ^ 2 := by
  rw [qform_compression, conj_eigenvectorUnitary Q hQ, qform_diagonal]

lemma conjTranspose_mul_eigenvectorUnitary (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ * (hQ.eigenvectorUnitary : Matrix m m 𝕜) = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hQ.eigenvectorUnitary

lemma eigenvectorUnitary_mul_conjTranspose (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜) * (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hQ.eigenvectorUnitary

lemma eigenvectorUnitary_mulVec_left_inv (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) (x : m → 𝕜) :
    (hQ.eigenvectorUnitary : Matrix m m 𝕜) *ᵥ
      ((hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ *ᵥ x) = x := by
  rw [mulVec_mulVec, eigenvectorUnitary_mul_conjTranspose Q hQ, one_mulVec]

/-- Multiplication by a unitary matrix preserves dimensions of subspaces. -/
lemma finrank_map_mulVecLin_eigenvectorUnitary (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian)
    (p : Submodule 𝕜 (m → 𝕜)) :
    Module.finrank 𝕜 (Submodule.map
        (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) p)
      = Module.finrank 𝕜 p := by
  have hc1 : (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) ∘ₗ
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, eigenvectorUnitary_mul_conjTranspose Q hQ, Matrix.mulVecLin_one]
  have hc2 : (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) ∘ₗ
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, conjTranspose_mul_eigenvectorUnitary Q hQ, Matrix.mulVecLin_one]
  have key := LinearEquiv.finrank_map_eq
    (LinearEquiv.ofLinear (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜))
      (Matrix.mulVecLin (hQ.eigenvectorUnitary : Matrix m m 𝕜)ᴴ) hc1 hc2) p
  simpa using key

/-- There is a subspace of dimension `posIndex Q` on which `Q` is positive definite. -/
lemma exists_posDefOn (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), Module.finrank 𝕜 S = posIndex Q ∧ PosDefOn Q S := by
  classical
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  set P : Finset m := {i : m | 0 < hQ.eigenvalues i}.toFinset with hP
  refine ⟨Submodule.map (Matrix.mulVecLin U) (coordSpace P), ?_, ?_⟩
  · rw [finrank_map_mulVecLin_eigenvectorUnitary Q hQ, finrank_coordSpace,
      posIndex_of_isHermitian hQ]
  · rintro x ⟨y, hy, rfl⟩ hx0
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx0 (by simp)
    obtain ⟨i₀, hi₀⟩ : ∃ i, y i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy0 (funext h)
    have hi₀P : i₀ ∈ P := by
      by_contra h
      exact hi₀ (coordSpace_apply_eq_zero hy h)
    have hval : Matrix.mulVecLin U y = U *ᵥ y := rfl
    rw [hval, qform_eigen Q hQ]
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · by_cases hi : i ∈ P
      · have : 0 < hQ.eigenvalues i := by
          simpa [hP, Set.mem_toFinset] using hi
        positivity
      · have : y i = 0 := coordSpace_apply_eq_zero hy hi
        simp [this]
    · have hpos : 0 < hQ.eigenvalues i₀ := by
        simpa [hP, Set.mem_toFinset] using hi₀P
      have : (0:ℝ) < ‖y i₀‖ ^ 2 := by positivity
      exact mul_pos hpos this

/-- Sylvester, hard direction: any subspace on which `Q` is positive definite has
dimension at most `posIndex Q`. -/
lemma finrank_le_posIndex (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (m → 𝕜)) (hS : PosDefOn Q S) :
    Module.finrank 𝕜 S ≤ posIndex Q := by
  classical
  set U : Matrix m m 𝕜 := (hQ.eigenvectorUnitary : Matrix m m 𝕜) with hU
  set P : Finset m := {i : m | 0 < hQ.eigenvalues i}.toFinset with hP
  set f : (m → 𝕜) →ₗ[𝕜] ({i // i ∈ P} → 𝕜) :=
    (LinearMap.pi (fun i : {i // i ∈ P} => (LinearMap.proj (i : m) : (m → 𝕜) →ₗ[𝕜] 𝕜))) ∘ₗ
      Matrix.mulVecLin Uᴴ
  have hfapply : ∀ (x : m → 𝕜) (i : {i // i ∈ P}), f x i = (Uᴴ *ᵥ x) (i : m) := by
    intro x i; rfl
  have hinj : Function.Injective (f.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxS⟩ hx
    have hx0 : ∀ i ∈ P, (Uᴴ *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (congrArg (fun (v : {i // i ∈ P} → 𝕜) => v) (LinearMap.mem_ker.mp hx))
        ⟨i, hi⟩
      simpa [hfapply] using this
    have hnonpos : qform Q x ≤ 0 := by
      have hxeq : U *ᵥ (Uᴴ *ᵥ x) = x := eigenvectorUnitary_mulVec_left_inv Q hQ x
      have := qform_eigen Q hQ (Uᴴ *ᵥ x)
      rw [hxeq] at this
      rw [this]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : i ∈ P
      · simp [hx0 i hi]
      · have hle : hQ.eigenvalues i ≤ 0 := by
          have : ¬ (0 < hQ.eigenvalues i) := by
            simpa [hP, Set.mem_toFinset] using hi
          linarith [not_lt.mp this]
        have : (0:ℝ) ≤ ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by positivity
        exact mul_nonpos_of_nonpos_of_nonneg hle this
    have : x = 0 := by
      by_contra hne
      exact absurd (hS x hxS hne) (not_lt.mpr hnonpos)
    simpa [Submodule.mem_bot, Subtype.ext_iff] using this
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [posIndex_of_isHermitian hQ, ← hP]
  calc Module.finrank 𝕜 S ≤ Module.finrank 𝕜 ({i // i ∈ P} → 𝕜) := hle
    _ = P.card := by simp [Module.finrank_fintype_fun_eq_card]

/-- **Inertia does not increase under compression**: for a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ Q B` is Hermitian and its positive index of
inertia is at most that of `Q`. -/
theorem posIndex_conj_le (Q : Matrix m m 𝕜) (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  classical
  have hQ' : (Bᴴ * Q * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  refine ⟨hQ', ?_⟩
  obtain ⟨S, hSrank, hSpos⟩ := exists_posDefOn (Bᴴ * Q * B) hQ'
  set T : Submodule 𝕜 (m → 𝕜) := Submodule.map (Matrix.mulVecLin B) S with hT
  have hmapmem : ∀ x ∈ S, Matrix.mulVecLin B x ∈ T := fun x hx => Submodule.mem_map_of_mem hx
  have hTpos : PosDefOn Q T := by
    rintro x ⟨y, hy, rfl⟩ hx0
    have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have : Matrix.mulVecLin B y = B *ᵥ y := rfl
    rw [this, qform_compression]
    exact hSpos y hy hy0
  have hrestrictinj : Function.Injective ((Matrix.mulVecLin B).restrict hmapmem) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨y, hyS⟩ hy
    have hBy : B *ᵥ y = 0 := by
      have := LinearMap.mem_ker.mp hy
      have h2 : (Matrix.mulVecLin B) y = 0 := by
        simpa [LinearMap.restrict_apply, Subtype.ext_iff] using this
      simpa using h2
    have : y = 0 := by
      by_contra hne
      have := hSpos y hyS hne
      rw [← qform_compression Q B y, hBy, qform_zero] at this
      exact lt_irrefl _ this
    simpa [Submodule.mem_bot, Subtype.ext_iff] using this
  have h1 : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 T :=
    LinearMap.finrank_le_finrank_of_injective hrestrictinj
  calc posIndex (Bᴴ * Q * B) = Module.finrank 𝕜 S := hSrank.symm
    _ ≤ Module.finrank 𝕜 T := h1
    _ ≤ posIndex Q := finrank_le_posIndex Q hQ T hTpos

/-! ### Sanity checks for `posIndex` -/

@[simp] lemma posIndex_zero : posIndex (0 : Matrix m m 𝕜) = 0 := by
  have h : (0 : Matrix m m 𝕜).IsHermitian := Matrix.isHermitian_zero
  have hev : ∀ i, h.eigenvalues i = 0 := by
    intro i; rw [h.eigenvalues_eq]; simp
  rw [posIndex_of_isHermitian h]
  simp [hev]

@[simp] lemma posIndex_one : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  have h : (1 : Matrix m m 𝕜).IsHermitian := Matrix.isHermitian_one
  have hev : ∀ i, h.eigenvalues i = 1 := by
    intro i
    rw [h.eigenvalues_eq]
    have hv : ‖h.eigenvectorBasis i‖ = 1 := h.eigenvectorBasis.orthonormal.1 i
    have hinner := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := 𝕜)
      (h.eigenvectorBasis i) (h.eigenvectorBasis i)
    simp only [one_mulVec, dotProduct_comm]
    rw [← hinner, inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [posIndex_of_isHermitian h]
  simp [hev]

end Zeta23Core

