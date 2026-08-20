/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : ℕ}

/-- A linear map between spaces of square complex matrices. -/
abbrev MatMap (n m : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ

/-- The Choi matrix of a linear map `Φ`:
`C_{(a,s),(b,t)} = Φ(E_{ab})_{s,t}`, i.e. `C = ∑_{a,b} E_{ab} ⊗ Φ(E_{ab})`. -/

def choiMatrix (Φ : MatMap n m) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The amplification `id_k ⊗ Φ`, acting blockwise on a `(k·n) × (k·n)` matrix. -/

def ampl (k : ℕ) (Φ : MatMap n m) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    Matrix (Fin k × Fin m) (Fin k × Fin m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: every amplification `id_k ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/

def IsCompletelyPositive (Φ : MatMap n m) : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ),
    X.PosSemidef → (ampl k Φ X).PosSemidef

/-- `id_k ⊗ V` for a rectangular matrix `V`. -/

def kronId (k : ℕ) (V : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin k × Fin m) (Fin k × Fin n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.2 q.2 else 0

/-- The (unnormalized) maximally entangled state `|ω⟩⟨ω|` with `ω = ∑_a e_a ⊗ e_a`. -/

def omegaMat (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then (1 : ℂ) else 0) * (if q.1 = q.2 then (1 : ℂ) else 0)

lemma omegaMat_posSemidef (n : ℕ) : (omegaMat n).PosSemidef := by
  have h : omegaMat n = (Matrix.of fun (_ : Unit) (p : Fin n × Fin n) =>
      (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ * (Matrix.of fun (_ : Unit) (p : Fin n × Fin n) =>
      (if p.1 = p.2 then (1 : ℂ) else 0)) := by
    ext p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, omegaMat, apply_ite (starRingEnd ℂ)]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma ampl_omegaMat (Φ : MatMap n m) : ampl n Φ (omegaMat n) = choiMatrix Φ := by
  ext p q
  simp only [ampl, choiMatrix, Matrix.of_apply]
  have h : (Matrix.of fun i j => omegaMat n (p.1, i) (q.1, j)) = Matrix.single p.1 q.1 1 := by
    ext i j
    simp only [omegaMat, Matrix.single_apply, Matrix.of_apply, ite_and, mul_ite, mul_one, mul_zero]
    split_ifs <;> rfl
  rw [h]

/-- The action of `Φ` is determined by its Choi matrix. -/

lemma apply_eq_sum_choiMatrix (Φ : MatMap n m) (A : Matrix (Fin n) (Fin n) ℂ) (s t : Fin m) :
    Φ A s t = ∑ a, ∑ b, A a b * choiMatrix Φ (a, s) (b, t) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply, choiMatrix, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : Matrix.single a b (A a b) = A a b • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.smul_single]; simp
  rw [h, map_smul]
  simp

/-- If `Φ` has a Kraus representation, its amplifications are conjugations by `id_k ⊗ V r`. -/

lemma ampl_of_kraus {ι : Type} [Fintype ι] (Φ : MatMap n m)
    (V : ι → Matrix (Fin m) (Fin n) ℂ) (hΦ : ∀ A, Φ A = ∑ r, V r * A * (V r)ᴴ)
    (k : ℕ) (X : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    ampl k Φ X = ∑ r, kronId k (V r) * X * (kronId k (V r))ᴴ := by
  ext p q
  obtain ⟨a, s⟩ := p
  obtain ⟨b, t⟩ := q
  simp only [ampl, Matrix.of_apply, hΦ, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kronId, Fintype.sum_prod_type, ite_mul, zero_mul, apply_ite,
    mul_zero, star_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

/-- Choi's theorem, hard direction: a positive semidefinite Choi matrix yields a Kraus
representation of `Φ`. -/

lemma kraus_of_choi_posSemidef (Φ : MatMap n m) (hC : (choiMatrix Φ).PosSemidef) :
    ∃ V : (Fin n × Fin m) → Matrix (Fin m) (Fin n) ℂ, ∀ A, Φ A = ∑ r, V r * A * (V r)ᴴ := by
  set B := CFC.sqrt (choiMatrix Φ) with hBdef
  have hBp : B.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hB : Bᴴ * B = choiMatrix Φ := by
    rw [hBp.1.eq]
    exact CFC.sqrt_mul_sqrt_self _ hC.nonneg
  refine ⟨fun r => Matrix.of fun s a => star (B r (a, s)), fun A => ?_⟩
  ext s t
  rw [apply_eq_sum_choiMatrix, ← hB]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, Finset.mul_sum, Finset.sum_mul]
  have key : ∀ g : Fin n → Fin n → (Fin n × Fin m) → ℂ,
      ∑ a, ∑ b, ∑ r, g a b r = ∑ r, ∑ a, ∑ b, g a b r := fun g =>
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [key (fun a b r => A a b * (star (B r (a, s)) * B r (b, t)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/

theorem choi_jamiolkowski (Φ : MatMap n m) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · intro hCP
    have h := hCP n (omegaMat n) (omegaMat_posSemidef n)
    rwa [ampl_omegaMat] at h
  · intro hC
    obtain ⟨V, hV⟩ := kraus_of_choi_posSemidef Φ hC
    intro k X hX
    rw [ampl_of_kraus Φ V hV k X]
    exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero (fun r _ => hX.mul_mul_conjTranspose_same _)

/-- Sanity check that the notions above are not degenerate: the Choi matrix of `-id` (on `1 × 1`
matrices) is not positive semidefinite, hence `-id` is not completely positive. -/
