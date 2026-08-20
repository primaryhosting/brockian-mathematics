import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras, acting on
`k × n` block matrices: the `(x, y)` block of `M` (an `n × n` matrix) is sent to the
`(x, y)` block of the result (an `m × m` matrix). -/
def ampl (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {k : Type*}
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* if all of its
amplifications `id_k ⊗ Φ` map positive semidefinite matrices to positive semidefinite
matrices. -/
def IsCP (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type u) [Fintype k] [DecidableEq k] (M : Matrix (k × n) (k × n) ℂ),
    M.PosSemidef → (ampl Φ M).PosSemidef

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`, i.e. the
matrix `(id ⊗ Φ) (|Ω⟩⟨Ω|)` where `|Ω⟩ = ∑ i, |i⟩ ⊗ |i⟩`, with entries
`C (i, a) (j, b) = Φ (single i j 1) a b`. -/
def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

omit [Fintype m] [DecidableEq m] in
/-- A linear map is determined by its Choi matrix: `Φ X` can be recovered by contracting
`X` with the Choi matrix. -/
lemma apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ) (a b : m) :
    Φ X a b = ∑ i, ∑ j, X i j * choi Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, choi, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    ext a b; simp [Matrix.single]
  rw [h, map_smul]
  simp

/-- The linear map reconstructed from a matrix `C` on `n × m`, by contracting `C` with the
input matrix. This is the inverse of `QI.choi`. -/
noncomputable def ofChoi (C : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun X := Matrix.of fun a b => ∑ i, ∑ j, X i j * C (i, a) (j, b)
  map_add' X Y := by
    ext a b
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    simp [Finset.mul_sum, mul_assoc]

/-- **The Choi–Jamiołkowski isomorphism** as a linear equivalence: linear maps
`Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ` correspond bijectively (and linearly) to matrices on
`n × m`, via the Choi matrix. -/
noncomputable def choiEquiv :
    (Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) ≃ₗ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun := choi
  map_add' Φ Ψ := by ext p q; simp [choi]
  map_smul' c Φ := by ext p q; simp [choi]
  invFun := ofChoi
  left_inv Φ := by
    ext X a b
    simpa [ofChoi] using (apply_eq_sum_choi Φ X a b).symm
  right_inv C := by
    ext p q
    simp [choi, ofChoi, Matrix.single, ite_and]

omit [Fintype m] [DecidableEq m] in
@[simp] lemma choiEquiv_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : choiEquiv Φ = choi Φ := rfl

/-- The maximally entangled (unnormalized) state `|Ω⟩⟨Ω|` as a matrix over `n × n`. -/
def omegaMat (n : Type u) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then (1 : ℂ) else 0) * (if q.1 = q.2 then (1 : ℂ) else 0)

lemma omegaMat_posSemidef : (omegaMat n).PosSemidef := by
  have h : omegaMat n = (Matrix.of fun (_ : Unit) (p : n × n) =>
      if p.1 = p.2 then (1 : ℂ) else 0)ᴴ * (Matrix.of fun (_ : Unit) (p : n × n) =>
      if p.1 = p.2 then (1 : ℂ) else 0) := by
    ext p q
    simp [omegaMat, Matrix.mul_apply, apply_ite (starRingEnd ℂ)]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [DecidableEq m] in
lemma ampl_omegaMat (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    ampl Φ (omegaMat n) = choi Φ := by
  ext p q
  have h : (Matrix.of fun i j => omegaMat n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext i j
    simp only [omegaMat, Matrix.of_apply, Matrix.single, ite_and, mul_ite, mul_one, mul_zero,
      eq_comm]
    split_ifs <;> rfl
  simp [ampl, choi, h]

/-- The Kraus operator (amplified by the identity on `k`) attached to the `r`-th row of a
factorization `choi Φ = Bᴴ * B`. -/
def krausAmpl (B : Matrix (n × m) (n × m) ℂ) (r : n × m) (k : Type*) [DecidableEq k] :
    Matrix (k × m) (k × n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (starRingEnd ℂ) (B r (q.2, p.2)) else 0

omit [DecidableEq m] in
/-- Kraus-type decomposition of the amplification, given a factorization `choi Φ = Bᴴ * B`. -/
lemma ampl_eq_sum_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (B : Matrix (n × m) (n × m) ℂ) (hB : choi Φ = Bᴴ * B)
    (k : Type*) [Fintype k] [DecidableEq k] (M : Matrix (k × n) (k × n) ℂ) :
    ampl Φ M = ∑ r : n × m, krausAmpl B r k * M * (krausAmpl B r k)ᴴ := by
  ext p q
  rw [Matrix.sum_apply]
  have hL : ampl Φ M p q =
      ∑ i, ∑ j, ∑ r : n × m,
        (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) (q.1, j) * B r (j, q.2) := by
    rw [ampl]
    simp only [Matrix.of_apply]
    rw [apply_eq_sum_choi]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hB]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [starRingEnd_apply]
    ring
  have hR : ∀ r : n × m, (krausAmpl B r k * M * (krausAmpl B r k)ᴴ) p q =
      ∑ i, ∑ j, (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) (q.1, j) * B r (j, q.2) := by
    intro r
    have hKM : ∀ (t : k × n), (krausAmpl B r k * M) p t
        = ∑ i, (starRingEnd ℂ) (B r (i, p.2)) * M (p.1, i) t := by
      intro t
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [krausAmpl, Matrix.of_apply, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hKM]
    simp only [krausAmpl, Matrix.of_apply, apply_ite (star : ℂ → ℂ), star_zero,
      starRingEnd_apply, star_star]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  rw [hL]
  simp only [hR]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  exact Finset.sum_comm

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCP Φ ↔ (choi Φ).PosSemidef := by
  constructor
  · intro h
    have := h n (omegaMat n) omegaMat_posSemidef
    rwa [ampl_omegaMat] at this
  · intro hC k _ _ M hM
    obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choi Φ = Bᴴ * B := by
      refine ⟨CFC.sqrt (choi Φ), ?_⟩
      have h1 : (CFC.sqrt (choi Φ)).PosSemidef :=
        Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
      rw [h1.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ hC.nonneg]
    rw [ampl_eq_sum_kraus Φ B hB k M]
    exact Matrix.posSemidef_sum _ fun r _ => hM.mul_mul_conjTranspose_same _

/-- The inverse form of the correspondence: under the Choi–Jamiołkowski isomorphism, the
linear map attached to a matrix `C` is completely positive exactly when `C` is positive
semidefinite. -/
theorem isCP_ofChoi_iff (C : Matrix (n × m) (n × m) ℂ) :
    IsCP (ofChoi C) ↔ C.PosSemidef := by
  have h : choi (ofChoi C) = C := choiEquiv.apply_symm_apply C
  rw [choi_jamiolkowski, h]

/-- The transposition map on `n × n` matrices, as a `ℂ`-linear map. -/
noncomputable def transposeMap (n : Type u) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (Matrix.transposeLinearEquiv n n ℂ ℂ).toLinearMap

/-- The Choi matrix of transposition on `2 × 2` matrices (the swap operator) is not positive
semidefinite. -/
lemma choi_transposeMap_not_posSemidef : ¬ (choi (transposeMap (Fin 2))).PosSemidef := by
  intro h
  have h2 := h.dotProduct_mulVec_nonneg
    (fun p : Fin 2 × Fin 2 => if p = (0, 1) then (1 : ℂ) else if p = (1, 0) then -1 else 0)
  simp [choi, transposeMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Matrix.single] at h2
  norm_num at h2

/-- Transposition is the standard example of a positive map that is not completely positive;
in particular `QI.IsCP` is not a vacuous condition. -/
theorem not_isCP_transposeMap : ¬ IsCP (transposeMap (Fin 2)) := by
  rw [choi_jamiolkowski]
  exact choi_transposeMap_not_posSemidef

end QI

