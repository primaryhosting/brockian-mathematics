/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The Choi–Jamiołkowski isomorphism

For a linear map `Φ` between finite-dimensional matrix algebras we prove that the following
are equivalent:

* `Φ` is completely positive (`QI.IsCP`), i.e. all amplifications `id ⊗ Φ` preserve positive
  semidefiniteness;
* the Choi matrix of `Φ` (`QI.choiMatrix`) is positive semidefinite;
* `Φ` admits a Kraus decomposition (`QI.HasKraus`).

The main statement is `QI.choi_jamiolkowski`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The amplification `id_{Fin k} ⊗ Φ` of a linear map `Φ` on matrices: it applies `Φ` to each
`m × m` block of a `(Fin k × m) × (Fin k × m)` matrix. -/
def amp (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (k : ℕ)
    (M : Matrix (Fin k × m) (Fin k × m) ℂ) : Matrix (Fin k × n) (Fin k × n) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => M (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* if all its amplifications
`id_{Fin k} ⊗ Φ` map positive semidefinite matrices to positive semidefinite matrices. -/
def IsCP (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k × m) (Fin k × m) ℂ), M.PosSemidef → (amp Φ k M).PosSemidef

/-- The Choi matrix of `Φ`, i.e. `∑ i j, E i j ⊗ Φ (E i j)`, written entrywise. -/
def choiMatrix (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix (m × n) (m × n) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- `Φ` admits a Kraus decomposition (with at most `card m * card n` Kraus operators). -/
def HasKraus (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Prop :=
  ∃ V : m × n → Matrix n m ℂ, ∀ X, Φ X = ∑ a, V a * X * (V a)ᴴ

section Aux

private theorem sum_comm3 {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    (f : ι → κ → σ → ℂ) : ∑ i, ∑ j, ∑ a, f i j a = ∑ a, ∑ i, ∑ j, f i j a :=
  calc ∑ i, ∑ j, ∑ a, f i j a
      = ∑ i, ∑ a, ∑ j, f i j a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, f i j a := Finset.sum_comm

omit [Fintype n] [DecidableEq n] in
private theorem conj_single (V : Matrix n m ℂ) (i j : m) (k l : n) :
    (V * Matrix.single i j (1 : ℂ) * Vᴴ) k l = V k i * (starRingEnd ℂ) (V l j) := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- The family of Kraus operators attached to a factor `B` of the Choi matrix. -/
private def krausMat (B : Matrix (m × n) (m × n) ℂ) (a : m × n) : Matrix n m ℂ :=
  Matrix.of fun k i => B (i, k) a

end Aux

omit [Fintype n] [DecidableEq n] in
/-- Every linear map is determined by its Choi matrix. -/
theorem apply_eq_sum_choi (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (X : Matrix m m ℂ) (p q : n) :
    Φ X p q = ∑ i, ∑ j, X i j * choiMatrix Φ (i, p) (j, q) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
        ext a b; simp [Matrix.single_apply]]
  rw [map_smul]
  simp [choiMatrix]

omit [DecidableEq n] in
/-- If `Φ` is given by the Kraus operators coming from `B`, then its Choi matrix is `B * Bᴴ`. -/
private theorem choi_eq_of_krausMat (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (B : Matrix (m × n) (m × n) ℂ)
    (h : ∀ X, Φ X = ∑ a, krausMat B a * X * (krausMat B a)ᴴ) : choiMatrix Φ = B * Bᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [choiMatrix, Matrix.of_apply, h, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun a _ => conj_single (krausMat B a) i j k l

omit [DecidableEq n] in
/-- If the Choi matrix of `Φ` factors as `B * Bᴴ`, then `B` provides Kraus operators for `Φ`. -/
private theorem krausMat_of_choi_eq (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (B : Matrix (m × n) (m × n) ℂ) (h : choiMatrix Φ = B * Bᴴ) :
    ∀ X, Φ X = ∑ a, krausMat B a * X * (krausMat B a)ᴴ := by
  intro X
  ext p q
  rw [apply_eq_sum_choi Φ X p q]
  calc ∑ i, ∑ j, X i j * choiMatrix Φ (i, p) (j, q)
      = ∑ i, ∑ j, ∑ a, X i j * (B (i, p) a * star (B (j, q) a)) := by
        simp only [h, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
    _ = ∑ j, ∑ i, ∑ a, X i j * (B (i, p) a * star (B (j, q) a)) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, X i j * (B (i, p) a * star (B (j, q) a)) := sum_comm3 _
    _ = (∑ a, krausMat B a * X * (krausMat B a)ᴴ) p q := by
        simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, krausMat,
          Matrix.of_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq n] in
/-- A map given by a Kraus decomposition has positive semidefinite Choi matrix. -/
theorem choi_posSemidef_of_hasKraus {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : HasKraus Φ) :
    (choiMatrix Φ).PosSemidef := by
  obtain ⟨V, hV⟩ := h
  set B : Matrix (m × n) (m × n) ℂ := Matrix.of fun p a => V a p.2 p.1 with hB
  have hkr : krausMat B = V := by
    funext a; ext k i; simp [krausMat, hB]
  rw [choi_eq_of_krausMat Φ B (by rw [hkr]; exact hV)]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- A map with positive semidefinite Choi matrix admits a Kraus decomposition. -/
theorem hasKraus_of_choi_posSemidef {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ}
    (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  set B : Matrix (m × n) (m × n) ℂ := CFC.sqrt (choiMatrix Φ) with hB
  have hBpsd : (0 : Matrix (m × n) (m × n) ℂ) ≤ B := CFC.sqrt_nonneg _
  have hfac : choiMatrix Φ = B * Bᴴ := by
    rw [hBpsd.posSemidef.isHermitian.eq, hB, CFC.sqrt_mul_sqrt_self _ h.nonneg]
  exact ⟨krausMat B, krausMat_of_choi_eq Φ B hfac⟩

omit [DecidableEq m] [DecidableEq n] in
/-- A map with a Kraus decomposition is completely positive: the amplification of `Φ` is given
by conjugation with the amplified Kraus operators `1 ⊗ V a`. -/
theorem isCP_of_hasKraus {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : HasKraus Φ) : IsCP Φ := by
  obtain ⟨V, hV⟩ := h
  intro k M hM
  set W : m × n → Matrix (Fin k × n) (Fin k × m) ℂ := fun a =>
    Matrix.of fun x y => if x.1 = y.1 then V a x.2 y.2 else 0 with hW
  have key : amp Φ k M = ∑ a, W a * M * (W a)ᴴ := by
    ext ⟨c, p⟩ ⟨d, q⟩
    simp only [amp, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hW, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      Finset.sum_ite_eq, Finset.sum_mul, mul_assoc, apply_ite (starRingEnd ℂ), mul_ite]
  rw [key]
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero fun a _ => hM.mul_mul_conjTranspose_same (W a)

omit [Fintype n] [DecidableEq n] in
/-- A completely positive map has positive semidefinite Choi matrix: the Choi matrix is, up to
reindexing, the image of the (positive semidefinite) maximally entangled state under the
amplification of `Φ`. -/
theorem choi_posSemidef_of_isCP {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (h : IsCP Φ) :
    (choiMatrix Φ).PosSemidef := by
  set K := Fintype.card m
  set e : m ≃ Fin K := Fintype.equivFin m
  -- the (unnormalised) maximally entangled state `|Ω⟩⟨Ω|`
  set v : Matrix (Fin K × m) Unit ℂ := Matrix.of fun x _ => if x.1 = e x.2 then 1 else 0 with hv
  set om : Matrix (Fin K × m) (Fin K × m) ℂ := v * vᴴ with hom
  have hamp := h K om (Matrix.posSemidef_self_mul_conjTranspose v)
  set E : m × n ≃ Fin K × n := e.prodCongr (Equiv.refl n) with hE
  have hblock : ∀ a b : Fin K,
      (Matrix.of fun i j => om (a, i) (b, j)) = Matrix.single (e.symm a) (e.symm b) (1 : ℂ) := by
    intro a b
    ext i j
    have h1 : (i = e.symm a) ↔ (a = e i) := by constructor <;> intro hx <;> simp [hx]
    have h2 : (j = e.symm b) ↔ (b = e j) := by constructor <;> intro hx <;> simp [hx]
    simp only [hom, hv, Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Finset.univ_unique, Finset.sum_const, Finset.card_singleton,
      one_smul, ite_and]
    split_ifs <;> simp_all
  have hsub : choiMatrix Φ = (amp Φ K om).submatrix ⇑E ⇑E := by
    ext ⟨i, p⟩ ⟨j, q⟩
    simp [choiMatrix, amp, Matrix.submatrix_apply, hE, hblock]
  rw [hsub]
  exact (Matrix.posSemidef_submatrix_equiv E).mpr hamp

/-- **Choi–Jamiołkowski isomorphism** (Choi's theorem on completely positive maps):
for a linear map `Φ` between (finite-dimensional) matrix algebras, the following are equivalent:
`Φ` is completely positive; the Choi matrix of `Φ` is positive semidefinite; `Φ` admits a Kraus
decomposition. -/
theorem choi_jamiolkowski (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) :
    List.TFAE [IsCP Φ, (choiMatrix Φ).PosSemidef, HasKraus Φ] := by
  tfae_have 1 → 2 := choi_posSemidef_of_isCP
  tfae_have 2 → 3 := hasKraus_of_choi_posSemidef
  tfae_have 3 → 1 := isCP_of_hasKraus
  tfae_finish

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

