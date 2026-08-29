/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Choi–Jamiołkowski

This file develops, for linear maps `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, the equivalence between

* complete positivity of `Φ` (every ampliation `Φ ⊗ id_k` preserves positive semidefiniteness),
* positive semidefiniteness of the Choi matrix `C(Φ)`,
* existence of a Kraus (operator sum) representation of `Φ`.
-/

namespace QI

open Matrix

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The Choi matrix of a linear map `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, given by
`C_{(i,a),(j,b)} = (Φ Eᵢⱼ)_{a b}` where `Eᵢⱼ` are the matrix units. -/
noncomputable def choiMatrix (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The ampliation `Φ ⊗ id_k`, acting on block matrices indexed by `m × k`. -/
def ampliation (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (k : Type) [Fintype k]
    (X : Matrix (m × k) (m × k) ℂ) : Matrix (n × k) (n × k) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (i, p.2) (j, q.2)) p.1 q.1

/-- Complete positivity: every ampliation `Φ ⊗ id_k` sends positive semidefinite matrices to
positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Matrix (m × k) (m × k) ℂ),
    X.PosSemidef → (ampliation Φ k X).PosSemidef

/-- `Φ` admits a Kraus (operator sum) representation `Φ X = ∑ s, Aₛ X Aₛᴴ`. -/
def HasKrausRepresentation (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Matrix n m ℂ), ∀ X, Φ X = ∑ s, A s * X * (A s)ᴴ

section Aux

omit [Fintype n] [DecidableEq n] in
/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
lemma posSemidef_sum {ι : Type} (s : Finset ι) (f : ι → Matrix n n ℂ)
    (h : ∀ i ∈ s, (f i).PosSemidef) : (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fintype m] in
lemma single_eq_smul (i j : m) (c : ℂ) :
    (Matrix.single i j c : Matrix m m ℂ) = c • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp [Matrix.single_apply]

omit [Fintype n] [DecidableEq n] in
/-- Every value of `Φ` is determined by its values on the matrix units. -/
lemma apply_eq_sum (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (X : Matrix m m ℂ) (a b : n) :
    Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
  have hX : X = ∑ i, ∑ j, (X i j) • (Matrix.single i j (1 : ℂ) : Matrix m m ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => single_eq_smul i j (X i j)
  conv_lhs => rw [hX]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  simp [Matrix.smul_apply, smul_eq_mul]

/-- A positive semidefinite matrix factors as `Bᴴ * B`. -/
lemma exists_conjTranspose_mul_self {N : Type} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℂ} (h : A.PosSemidef) : ∃ B : Matrix N N ℂ, A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr h)
  exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩

end Aux

section CPtoChoi

/-- The (unnormalised) maximally entangled vector `∑ i, |i⟩ ⊗ |i⟩`. -/
noncomputable def entVec : Matrix (m × m) Unit ℂ :=
  Matrix.of fun p _ => if p.1 = p.2 then 1 else 0

/-- The (unnormalised) maximally entangled state `|ω⟩⟨ω|`. -/
noncomputable def maxEnt : Matrix (m × m) (m × m) ℂ :=
  (entVec : Matrix (m × m) Unit ℂ) * entVecᴴ

lemma maxEnt_posSemidef : (maxEnt : Matrix (m × m) (m × m) ℂ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

omit [Fintype m] in
lemma maxEnt_apply (p q : m × m) :
    (maxEnt : Matrix (m × m) (m × m) ℂ) p q =
      (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0) := by
  simp [maxEnt, entVec, Matrix.mul_apply, Matrix.conjTranspose_apply]

omit [Fintype n] [DecidableEq n] in
/-- The ampliation of `Φ` applied to the maximally entangled state is the Choi matrix, up to
the swap of the two tensor factors. -/
lemma ampliation_maxEnt (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    ampliation Φ m maxEnt = (choiMatrix Φ).submatrix Prod.swap Prod.swap := by
  ext p q
  have h : (Matrix.of fun i j => (maxEnt : Matrix (m × m) (m × m) ℂ) (i, p.2) (j, q.2)) =
      Matrix.single p.2 q.2 (1 : ℂ) := by
    ext i j
    rw [Matrix.of_apply, maxEnt_apply, Matrix.single_apply]
    by_cases h1 : i = p.2 <;> by_cases h2 : j = q.2 <;>
      simp [h1, h2, eq_comm, and_comm]
  simp [ampliation, choiMatrix, Matrix.submatrix_apply, h]

omit [Fintype n] [DecidableEq n] in
lemma cp_imp_choi_posSemidef (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have h1 : (ampliation Φ m (maxEnt : Matrix (m × m) (m × m) ℂ)).PosSemidef :=
    h m maxEnt maxEnt_posSemidef
  rw [ampliation_maxEnt] at h1
  have h2 := h1.submatrix (Prod.swap : m × n → n × m)
  have h3 : ((choiMatrix Φ).submatrix Prod.swap Prod.swap).submatrix
      (Prod.swap : m × n → n × m) Prod.swap = choiMatrix Φ := by
    ext p q
    simp [Matrix.submatrix_apply]
  rwa [h3] at h2

end CPtoChoi

section ChoiToKraus

lemma choi_posSemidef_imp_kraus (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : (choiMatrix Φ).PosSemidef) : HasKrausRepresentation Φ := by
  classical
  obtain ⟨B, hB⟩ := exists_conjTranspose_mul_self h
  set e := Fintype.equivFin (m × n) with he
  refine ⟨Fintype.card (m × n),
    fun s => Matrix.of fun k i => starRingEnd ℂ (B (e.symm s) (i, k)), ?_⟩
  intro X
  ext a b
  rw [apply_eq_sum Φ X a b, Matrix.sum_apply]
  have hC : ∀ i j : m, Φ (Matrix.single i j 1) a b
      = ∑ p : m × n, starRingEnd ℂ (B p (i, a)) * B p (j, b) := by
    intro i j
    have hij := congrFun (congrFun hB (i, a)) (j, b)
    simpa [choiMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using hij
  have swap3 : ∀ (g : (m × n) → m → m → ℂ),
      ∑ i, ∑ j, ∑ p, g p i j = ∑ p, ∑ i, ∑ j, g p i j := by
    intro g
    have h1 : ∀ i : m, ∑ j, ∑ p, g p i j = ∑ p, ∑ j, g p i j := fun _ => Finset.sum_comm
    simp_rw [h1]
    exact Finset.sum_comm
  have step1 : ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b
      = ∑ p : m × n, ∑ i, ∑ j, X i j * (starRingEnd ℂ (B p (i, a)) * B p (j, b)) := by
    simp_rw [hC, Finset.mul_sum]
    exact swap3 _
  rw [step1, ← Equiv.sum_comp e.symm
    (fun p : m × n => ∑ i, ∑ j, X i j * (starRingEnd ℂ (B p (i, a)) * B p (j, b)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, Complex.conj_conj]
  ring

end ChoiToKraus

section KrausToCP

omit [DecidableEq m] [DecidableEq n] in
lemma kraus_imp_cp (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : HasKrausRepresentation Φ) : IsCompletelyPositive Φ := by
  classical
  obtain ⟨r, A, hA⟩ := h
  intro k _ X hX
  have hEq : ampliation Φ k X =
      ∑ s, (Matrix.of fun (u : n × k) (v : m × k) =>
              A s u.1 v.1 * (if u.2 = v.2 then 1 else 0) : Matrix (n × k) (m × k) ℂ) * X *
            (Matrix.of fun (u : n × k) (v : m × k) =>
              A s u.1 v.1 * (if u.2 = v.2 then 1 else 0) : Matrix (n × k) (m × k) ℂ)ᴴ := by
    ext p q
    rw [ampliation, Matrix.of_apply, hA, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, RCLike.star_def, apply_ite, map_zero, Finset.sum_mul,
      ite_mul, zero_mul, mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hEq]
  exact posSemidef_sum _ _ fun s _ => hX.mul_mul_conjTranspose_same _

end KrausToCP

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨cp_imp_choi_posSemidef Φ, fun h => kraus_imp_cp Φ (choi_posSemidef_imp_kraus Φ h)⟩

/-- The three standard characterisations of completely positive maps between matrix algebras:
complete positivity, positivity of the Choi matrix, and existence of a Kraus representation. -/
theorem choi_jamiolkowski_tfae (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    [IsCompletelyPositive Φ, (choiMatrix Φ).PosSemidef, HasKrausRepresentation Φ].TFAE := by
  tfae_have 1 → 2 := cp_imp_choi_posSemidef Φ
  tfae_have 2 → 3 := choi_posSemidef_imp_kraus Φ
  tfae_have 3 → 1 := kraus_imp_cp Φ
  tfae_finish

section Example

/-- The transpose map on `2 × 2` complex matrices. -/
noncomputable def transposeMap :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := Xᵀ
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The Choi matrix of the transpose map (the swap operator) is not positive semidefinite;
in particular `IsCompletelyPositive` is not a vacuous condition. -/
theorem transposeMap_not_completelyPositive : ¬ IsCompletelyPositive transposeMap := by
  rw [choi_jamiolkowski]
  intro h
  have hd := h.dotProduct_mulVec_nonneg
    (fun p : Fin 2 × Fin 2 => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0)
  simp [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Matrix.single_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ] at hd
  norm_num at hd

end Example

end QI

