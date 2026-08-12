import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
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

namespace QI

open Matrix
open scoped ComplexOrder
open scoped MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`:
the block matrix whose `(a, b)` block is `Φ (single a b 1)`, i.e.
`Choi Φ = (id ⊗ Φ) (|Ω⟩⟨Ω|)` for the unnormalised maximally entangled vector `Ω`. -/
def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The ampliation `id_k ⊗ Φ` of `Φ`, acting on `k × k` block matrices with `n × n` blocks
by applying `Φ` to each block. -/
def ampliation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (k : Type) [Fintype k] [DecidableEq k]
    (A : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun s t => A (p.1, s) (q.1, t)) p.2 q.2

/-- `Φ` is completely positive: every ampliation `id_k ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) [Fintype k] [DecidableEq k] (A : Matrix (k × n) (k × n) ℂ),
    A.PosSemidef → (ampliation Φ k A).PosSemidef

/-- Swapping the order of a triple sum. -/
private lemma sum_comm_three {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  have h1 : ∀ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, f a b c := fun a => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix determines the map. -/
lemma apply_apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (X : Matrix n n ℂ) (i j : m) :
    Φ X i j = ∑ a, ∑ b, X a b * choi Φ (a, i) (b, j) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h : Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
    ext s t
    simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    split <;> simp
  rw [h, map_smul]
  simp [choi]

/-- The unnormalised maximally entangled state `|Ω⟩⟨Ω|`, `Ω = ∑ i, e i ⊗ e i`. -/
noncomputable def maxEntangled (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.replicateCol (Fin 1) (fun p : n × n => if p.1 = p.2 then (1:ℂ) else 0) *
    (Matrix.replicateCol (Fin 1) (fun p : n × n => if p.1 = p.2 then (1:ℂ) else 0))ᴴ

lemma maxEntangled_posSemidef : (maxEntangled n).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

omit [Fintype m] [DecidableEq m] in
lemma choi_eq_ampliation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    choi Φ = ampliation Φ n (maxEntangled n) := by
  ext p q
  simp only [choi, ampliation, Matrix.of_apply]
  have key : (Matrix.of fun s t => maxEntangled n (p.1, s) (q.1, t))
      = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext s t
    simp only [maxEntangled, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.replicateCol_apply, Matrix.of_apply, Matrix.single_apply]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    by_cases h1 : p.1 = s <;> by_cases h2 : q.1 = t <;> simp [h1, h2]
  rw [key]

/-- Choi's theorem: a positive semidefinite Choi matrix yields a Kraus decomposition. -/
lemma exists_kraus_of_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choi Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ X : Matrix n n ℂ, Φ X = ∑ c, V c * X * (V c)ᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun c => Matrix.of fun i a => star (B c (a, i)), fun X => ?_⟩
  ext i j
  rw [apply_apply_eq_sum_choi]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, hB, Matrix.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_three (fun a b c => X a b * (star (B c (a, i)) * B c (b, j)))]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus decomposition `X ↦ ∑ c, V c * X * (V c)ᴴ` is completely positive. -/
lemma ampliation_posSemidef_of_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (V : (n × m) → Matrix m n ℂ) (hV : ∀ X : Matrix n n ℂ, Φ X = ∑ c, V c * X * (V c)ᴴ) :
    IsCompletelyPositive Φ := by
  intro k _ _ A hA
  set W : (n × m) → Matrix (k × m) (k × n) ℂ :=
    fun c => Matrix.of fun x y => if x.1 = y.1 then V c x.2 y.2 else 0 with hW
  have key : ampliation Φ k A = ∑ c, W c * A * (W c)ᴴ := by
    ext p q
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hW, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero, apply_ite (star : ℂ → ℂ),
      star_zero]
    have h1 : ∀ (x : k) (x1 : n) (x2 : k),
        (∑ x3, if p.1 = x2 then V c p.2 x3 * A (x2, x3) (x, x1) else 0) =
          if p.1 = x2 then ∑ x3, V c p.2 x3 * A (x2, x3) (x, x1) else 0 := by
      intro x x1 x2; split_ifs <;> simp
    simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 : ∀ x : k,
        (∑ x1, if q.1 = x then (∑ x3, V c p.2 x3 * A (p.1, x3) (x, x1)) * star (V c q.2 x1)
          else 0) =
          if q.1 = x then ∑ x1, (∑ x3, V c p.2 x3 * A (p.1, x3) (x, x1)) * star (V c q.2 x1)
          else 0 := by
      intro x; split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]
  exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
    (fun c _ => hA.mul_mul_conjTranspose_same (W c))

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choi Φ).PosSemidef := by
  constructor
  · intro hcp
    rw [choi_eq_ampliation]
    exact hcp n (maxEntangled n) maxEntangled_posSemidef
  · intro h
    obtain ⟨V, hV⟩ := exists_kraus_of_choi_posSemidef Φ h
    exact ampliation_posSemidef_of_kraus Φ V hV

end QI

