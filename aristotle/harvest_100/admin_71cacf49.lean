import Mathlib
/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators MatrixOrder
open Matrix ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_k ⊗ Φ` of a linear map `Φ` between matrix algebras:
its `((a, p), (b, q))` entry is the `(p, q)` entry of `Φ` applied to the `(a, b)` block. -/
def ampl (k : Type) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (X : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* when all of its
amplifications `id_k ⊗ Φ` (for finite `k`) map positive semidefinite matrices to
positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Matrix (k × n) (k × n) ℂ),
    X.PosSemidef → (ampl k Φ X).PosSemidef

/-- The Choi matrix of `Φ`, i.e. `∑ i j, E i j ⊗ Φ (E i j)`: its `((i, p), (j, q))` entry
is `Φ (single i j 1) p q`. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- `Φ` admits a Kraus decomposition `Φ X = ∑ a, K a * X * (K a)ᴴ`. -/
def HasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix m n ℂ),
    ∀ X : Matrix n n ℂ, Φ X = ∑ a, K a * X * (K a)ᴴ

/-- The (unnormalized) maximally entangled state `∑ i j, E i j ⊗ E i j`. -/
def maxEnt (n : Type) [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

lemma maxEnt_posSemidef : (maxEnt n).PosSemidef := by
  have h : maxEnt n
      = (Matrix.of fun (_ : Unit) (q : n × n) => if q.1 = q.2 then (1 : ℂ) else 0)ᴴ *
        (Matrix.of fun (_ : Unit) (q : n × n) => if q.1 = q.2 then (1 : ℂ) else 0) := by
    ext p q
    simp only [maxEnt, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, ite_and,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype n] [Fintype m] [DecidableEq m] in
/-- Applying `id ⊗ Φ` to the maximally entangled state produces the Choi matrix. -/
lemma ampl_maxEnt_eq_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    ampl n Φ (maxEnt n) = choiMatrix Φ := by
  ext p q
  have h : (Matrix.of fun i j => maxEnt n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext i j
    simp [maxEnt, Matrix.single_apply]
  simp [ampl, choiMatrix, h]

omit [Fintype m] [DecidableEq m] in
/-- A completely positive map has positive semidefinite Choi matrix. -/
lemma choiMatrix_posSemidef_of_cp {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have hn := h n (maxEnt n) maxEnt_posSemidef
  rwa [ampl_maxEnt_eq_choiMatrix] at hn

/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` has a Kraus decomposition. -/
lemma hasKraus_of_choiMatrix_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choiMatrix Φ = Bᴴ * B := by
    have h0 : (0 : Matrix (n × m) (n × m) ℂ) ≤ choiMatrix Φ := Matrix.nonneg_iff_posSemidef.mpr h
    refine ⟨CFC.sqrt (choiMatrix Φ), ?_⟩
    have h1 : (CFC.sqrt (choiMatrix Φ))ᴴ = CFC.sqrt (choiMatrix Φ) :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
    rw [h1, CFC.sqrt_mul_sqrt_self _ h0]
  refine ⟨n × m, inferInstance, fun a => Matrix.of fun (k : m) (i : n) => star (B a (i, k)), ?_⟩
  intro X
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq =>
      simp only [map_add, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Matrix.add_mul, Matrix.mul_add]
  | h_std_basis i j c =>
      have hsingle : (Matrix.single i j c : Matrix n n ℂ) = c • Matrix.single i j (1 : ℂ) := by
        ext a b; simp [Matrix.single_apply]
      rw [hsingle, map_smul]
      ext k l
      have hC : Φ (Matrix.single i j (1 : ℂ)) k l = choiMatrix Φ (i, k) (j, l) := rfl
      simp only [Matrix.smul_apply, smul_eq_mul, hC, hB, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.single_apply, star_star]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_ite, ite_and, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      ring

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus decomposition is completely positive. -/
lemma cp_of_hasKraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : HasKraus Φ) :
    IsCompletelyPositive Φ := by
  obtain ⟨ι, hι, K, hK⟩ := h
  intro k _ X hX
  classical
  have hsum : ampl k Φ X
      = ∑ a, (Matrix.of fun (u : k × m) (v : k × n) => if u.1 = v.1 then K a u.2 v.2 else 0) * X
          * (Matrix.of fun (u : k × m) (v : k × n) => if u.1 = v.1 then K a u.2 v.2 else 0)ᴴ := by
    ext p q
    simp only [ampl, hK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Fintype.sum_prod_type, apply_ite (star : ℂ → ℂ), star_zero, ite_mul,
      zero_mul, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    simp
  rw [hsum]
  refine Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero ?_
  intro a _
  exact hX.mul_mul_conjTranspose_same _

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨choiMatrix_posSemidef_of_cp, fun h => cp_of_hasKraus (hasKraus_of_choiMatrix_posSemidef h)⟩

/-- A linear map between matrix algebras is completely positive iff it has a Kraus
decomposition `Φ X = ∑ a, K a * X * (K a)ᴴ`. -/
theorem isCompletelyPositive_iff_hasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ HasKraus Φ :=
  ⟨fun h => hasKraus_of_choiMatrix_posSemidef (choiMatrix_posSemidef_of_cp h), cp_of_hasKraus⟩

/-! ### Sanity checks: the identity map is completely positive, the transpose map is not -/

/-- The identity map on matrices is completely positive. -/
theorem id_isCompletelyPositive :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  cp_of_hasKraus ⟨Unit, inferInstance, fun _ => 1, by intro X; simp⟩

/-- The transpose map on `n × n` matrices. -/
def transposeMap (n : Type) [Fintype n] : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := Xᵀ
  map_add' _ _ := Matrix.transpose_add _ _
  map_smul' _ _ := Matrix.transpose_smul _ _

/-- The transpose map on `2 × 2` matrices is not completely positive: its Choi matrix
(the swap operator) is not positive semidefinite. -/
theorem transposeMap_not_isCompletelyPositive :
    ¬ IsCompletelyPositive (transposeMap (Fin 2)) := by
  rw [choi_jamiolkowski]
  intro h
  have hv := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2
    (fun p : Fin 2 × Fin 2 => if p = (0, 1) then (1 : ℂ) else if p = (1, 0) then -1 else 0)
  simp only [choiMatrix, transposeMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.single_apply, Matrix.transpose_apply, Pi.star_apply, Prod.mk.injEq] at hv
  norm_num at hv

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

