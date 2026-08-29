import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The ampliation `idₖ ⊗ Φ`, acting on `k × k` block matrices with `n × n` blocks by
applying `Φ` to each block. -/
def ampliation (k : Type) [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (k × n) (k × n) ℂ) :
    Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map is completely positive when all its ampliations `idₖ ⊗ Φ` map positive
semidefinite matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] [DecidableEq k] (X : Matrix (k × n) (k × n) ℂ),
    X.PosSemidef → (ampliation k Φ X).PosSemidef

/-- `Φ` admits a Kraus representation `Φ X = ∑ c, V c * X * (V c)ᴴ`
(with the Kraus family indexed by `n × m`, which is enough). -/
def HasKrausRepresentation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ V : n × m → Matrix m n ℂ, ∀ X, Φ X = ∑ c, V c * X * (V c)ᴴ

section Helpers

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
lemma posSemidef_sum {k ι : Type} [Fintype k] (s : Finset ι)
    (f : ι → Matrix k k ℂ) (hf : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Matrix.PosSemidef.zero (n := k) (R := ℂ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The entries of a single Kraus term `V * X * Vᴴ`. -/
lemma kraus_term_entry {α β : Type} [Fintype α] [Fintype β]
    (V : Matrix β α ℂ) (X : Matrix α α ℂ) (a b : β) :
    (V * X * Vᴴ) a b = ∑ i, ∑ j, X i j * (V a i * (starRingEnd ℂ) (V b j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq n] [DecidableEq m] in
/-- Reordering a triple sum. -/
lemma sum_swap3 (f : (n × m) → n → n → ℂ) :
    ∑ c, ∑ i, ∑ j, f c i j = ∑ i, ∑ j, ∑ c, f c i j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

omit [Fintype m] [DecidableEq m] in
/-- A linear map is completely determined by its Choi matrix. -/
lemma apply_entry_eq_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (a b : m) : Φ X a b = ∑ i, ∑ j, X i j * choiMatrix Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [show ∀ i j, Matrix.single i j (X i j) = X i j • Matrix.single (n := n) i j 1 from
      fun i j => by simp [Matrix.smul_single], map_sum, map_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, choiMatrix, Matrix.of_apply]

/-- The block-diagonal ampliation `1ₖ ⊗ V` of a Kraus operator. -/
def krausAmp (k : Type) [DecidableEq k] (V : Matrix m n ℂ) : Matrix (k × m) (k × n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.2 q.2 else 0

omit [DecidableEq n] [DecidableEq m] in
/-- Collapsing the sums over `k × n` coming from a block-diagonal conjugation. -/
lemma sum_prod_collapse {k : Type} [Fintype k] [DecidableEq k]
    (X : Matrix (k × n) (k × n) ℂ) (r s : k) (g h : n → ℂ) :
    (∑ u : k × n, ∑ v : k × n, X u v *
      ((if r = u.1 then g u.2 else 0) * (if s = v.1 then h v.2 else 0)))
      = ∑ i, ∑ j, X (r, i) (s, j) * (g i * h j) := by
  simp [Fintype.sum_prod_type, ite_mul, mul_ite, Finset.sum_ite_eq]

end Helpers

omit [DecidableEq m] in
/-- A map with a Kraus representation has a positive semidefinite Choi matrix. -/
lemma choiMatrix_posSemidef_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : HasKrausRepresentation Φ) : (choiMatrix Φ).PosSemidef := by
  obtain ⟨V, hV⟩ := h
  set A : Matrix (n × m) (n × m) ℂ :=
    Matrix.of fun c q => (starRingEnd ℂ) (V c q.2 q.1) with hA
  have key : choiMatrix Φ = Aᴴ * A := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [choiMatrix, Matrix.of_apply, hV, Matrix.sum_apply, kraus_term_entry,
      Matrix.conjTranspose_apply, hA]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  rw [key]
  exact Matrix.posSemidef_conjTranspose_mul_self A

/-- If the Choi matrix is positive semidefinite then `Φ` has a Kraus representation. -/
lemma hasKrausRepresentation_of_choiMatrix_posSemidef
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : (choiMatrix Φ).PosSemidef) :
    HasKrausRepresentation Φ := by
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  refine ⟨fun c => Matrix.of fun a i => (starRingEnd ℂ) (B c (i, a)), fun X => ?_⟩
  ext a b
  rw [apply_entry_eq_choi, Matrix.sum_apply]
  simp only [kraus_term_entry, Matrix.of_apply, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [sum_swap3]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [hB]
  simp [Matrix.mul_apply, Matrix.star_apply]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus representation is completely positive. -/
lemma isCompletelyPositive_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : HasKrausRepresentation Φ) : IsCompletelyPositive Φ := by
  obtain ⟨V, hV⟩ := h
  intro k _ _ X hX
  have key : ampliation k Φ X
      = ∑ c, krausAmp k (V c) * X * (krausAmp k (V c))ᴴ := by
    ext p q
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply, kraus_term_entry]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 := sum_prod_collapse (n := n) X p.1 q.1 (fun i => V c p.2 i)
      (fun j => (starRingEnd ℂ) (V c q.2 j))
    simpa only [krausAmp, Matrix.of_apply, apply_ite (starRingEnd ℂ), map_zero] using h1.symm
  rw [key]
  exact posSemidef_sum _ _ fun c _ => hX.mul_mul_conjTranspose_same _

omit [Fintype m] [DecidableEq m] in
/-- A completely positive map has a positive semidefinite Choi matrix:
the Choi matrix is the image of the (unnormalized) maximally entangled state. -/
lemma choiMatrix_posSemidef_of_completelyPositive
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (h : IsCompletelyPositive Φ) :
    (choiMatrix Φ).PosSemidef := by
  set A : Matrix Unit (n × n) ℂ := Matrix.of fun _ p => if p.1 = p.2 then 1 else 0 with hA
  set Om : Matrix (n × n) (n × n) ℂ := Aᴴ * A with hOm
  have hOmPSD : Om.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have key : ampliation n Φ Om = choiMatrix Φ := by
    ext p q
    have hblock : (Matrix.of fun i j => Om (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 (1 : ℂ) := by
      ext i j
      simp only [hOm, hA, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
        Matrix.single_apply, Finset.univ_unique, Finset.sum_singleton, RCLike.star_def]
      split_ifs <;> simp_all
    simp [ampliation, choiMatrix, hblock]
  rw [← key]
  exact h n Om hOmPSD

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite; equivalently, iff it
admits a Kraus representation. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef) ∧
      (IsCompletelyPositive Φ ↔ HasKrausRepresentation Φ) := by
  have h1 : IsCompletelyPositive Φ → (choiMatrix Φ).PosSemidef :=
    choiMatrix_posSemidef_of_completelyPositive
  have h2 : (choiMatrix Φ).PosSemidef → HasKrausRepresentation Φ :=
    hasKrausRepresentation_of_choiMatrix_posSemidef
  have h3 : HasKrausRepresentation Φ → IsCompletelyPositive Φ :=
    isCompletelyPositive_of_kraus
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end QI

#print axioms QI.choi_jamiolkowski

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

