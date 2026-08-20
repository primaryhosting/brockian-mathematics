import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder MatrixOrder

namespace QI

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The partial trace over the second (environment) tensor factor. -/
noncomputable def ptraceRight {B E : Type} [Fintype E] (M : Matrix (B × E) (B × E) ℂ) :
    Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ x : E, M (b, x) (b', x)

/-- Complete positivity of a linear map between matrix algebras: for every `k`, the
amplified map `id_{Fin k} ⊗ Φ` sends positive semidefinite matrices to positive
semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k × A) (Fin k × A) ℂ), M.PosSemidef →
    (Matrix.of fun x y : Fin k × B =>
      Φ (Matrix.of fun a a' => M (x.1, a) (y.1, a')) x.2 y.2).PosSemidef

/-- Trace preservation. -/
def IsTracePreserving (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ ρ : Matrix A A ℂ, (Φ ρ).trace = ρ.trace

private lemma trace_mul_single (M : Matrix A A ℂ) (a a' : A) :
    (M * Matrix.single a' a 1).trace = M a a' := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq]

private lemma trace_single_one (a a' : A) :
    (Matrix.single a' a (1 : ℂ)).trace = if a = a' then 1 else 0 := by
  simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

omit [Fintype A] [DecidableEq A] in
/-- Sanity check: the identity channel is completely positive. -/
theorem id_isCompletelyPositive :
    IsCompletelyPositive (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := by
  intro k M hM
  have : (Matrix.of fun x y : Fin k × A =>
      (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
        (Matrix.of fun a a' => M (x.1, a) (y.1, a')) x.2 y.2) = M := rfl
  rw [this]
  exact hM

omit [DecidableEq A] in
/-- Sanity check: the identity channel is trace preserving. -/
theorem id_isTracePreserving :
    IsTracePreserving (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := fun _ => rfl

omit [Fintype B] [DecidableEq B] in
/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem choi_posSemidef (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hcp : IsCompletelyPositive Φ) :
    (Matrix.of fun x y : A × B => Φ (Matrix.single x.1 y.1 1) x.2 y.2).PosSemidef := by
  classical
  set n := Fintype.card A with hn
  set σ : A ≃ Fin n := Fintype.equivFin A with hσ
  set v : Fin n × A → ℂ := fun p => if σ.symm p.1 = p.2 then 1 else 0 with hv
  have hM : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have h1 := hcp n _ hM
  have h2 := h1.submatrix (fun p : A × B => (σ p.1, p.2))
  have key : ∀ a a' : A, (Matrix.of fun x x' : A =>
      (Matrix.vecMulVec v (star v)) (σ a, x) (σ a', x')) = Matrix.single a a' (1 : ℂ) := by
    intro a a'
    ext x x'
    simp only [hv, Matrix.vecMulVec, Matrix.of_apply, Matrix.single_apply, Pi.star_apply,
      Equiv.symm_apply_apply, ite_and]
    split_ifs with h1 h2 h3 <;> simp_all [eq_comm]
  have heq : (Matrix.of fun x y : A × B => Φ (Matrix.single x.1 y.1 1) x.2 y.2)
      = (Matrix.of fun x y : Fin n × B =>
        Φ (Matrix.of fun a a' => (Matrix.vecMulVec v (star v)) (x.1, a) (y.1, a')) x.2 y.2).submatrix
          (fun p : A × B => (σ p.1, p.2)) (fun p : A × B => (σ p.1, p.2)) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [key x.1 y.1]
  rw [heq]
  exact h2

/-- Kraus decomposition of a completely positive map. -/
theorem exists_kraus (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hcp : IsCompletelyPositive Φ) :
    ∃ K : A × B → Matrix B A ℂ, ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ μ, K μ * ρ * (K μ)ᴴ := by
  classical
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr (choi_posSemidef Φ hcp))
  refine ⟨fun μ => Matrix.of fun b a => starRingEnd ℂ (D μ (a, b)), ?_⟩
  have hDapply : ∀ x y : A × B, Φ (Matrix.single x.1 y.1 1) x.2 y.2
      = ∑ μ, starRingEnd ℂ (D μ x) * D μ y := by
    intro x y
    have := congrArg (fun M => M x y) hD
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.star_apply] using this
  intro ρ
  have hΦ : Φ ρ = ∑ a : A, ∑ a' : A, (ρ a a') • Φ (Matrix.single a a' 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [show Matrix.single a a' (ρ a a') = (ρ a a') • Matrix.single a a' (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  ext b b'
  rw [hΦ]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply]
  calc ∑ a : A, ∑ a' : A, ρ a a' * Φ (Matrix.single a a' 1) b b'
      = ∑ a : A, ∑ a' : A, ∑ μ : A × B,
          starRingEnd ℂ (D μ (a, b)) * ρ a a' * D μ (a', b') :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
          rw [hDapply (a, b) (a', b'), Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring
    _ = ∑ a : A, ∑ μ : A × B, ∑ a' : A,
          starRingEnd ℂ (D μ (a, b)) * ρ a a' * D μ (a', b') :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ μ : A × B, ∑ a : A, ∑ a' : A,
          starRingEnd ℂ (D μ (a, b)) * ρ a a' * D μ (a', b') := Finset.sum_comm
    _ = ∑ μ : A × B, ∑ a' : A, ∑ a : A,
          starRingEnd ℂ (D μ (a, b)) * ρ a a' * D μ (a', b') :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ μ : A × B, ∑ a' : A,
          (∑ a : A, starRingEnd ℂ (D μ (a, b)) * ρ a a') * star (starRingEnd ℂ (D μ (a', b'))) :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun a' _ => by
          rw [Finset.sum_mul]; simp

omit [DecidableEq B] in
/-- For a trace preserving map, the Kraus operators satisfy the completeness relation. -/
theorem kraus_sum_conjTranspose_mul_self {ι : Type} [Fintype ι] (K : ι → Matrix B A ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (htp : IsTracePreserving Φ)
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ μ, K μ * ρ * (K μ)ᴴ) :
    ∑ μ, (K μ)ᴴ * K μ = 1 := by
  have key : ∀ ρ : Matrix A A ℂ, ((∑ μ, (K μ)ᴴ * K μ) * ρ).trace = ρ.trace := by
    intro ρ
    have h := htp ρ
    rw [hK ρ] at h
    rw [Finset.sum_mul, Matrix.trace_sum]
    rw [Matrix.trace_sum] at h
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  ext a a'
  have h := key (Matrix.single a' a 1)
  rw [trace_mul_single, trace_single_one] at h
  rw [h, Matrix.one_apply]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- Any finite family of matrices can be re-indexed by `Fin (k+1)`, padding with zeros. -/
theorem exists_fin_reindex {ι : Type} [Fintype ι] (K : ι → Matrix B A ℂ) :
    ∃ (k : ℕ) (G : Fin (k + 1) → Matrix B A ℂ),
      ∀ {M : Type} [AddCommMonoid M] (f : Matrix B A ℂ → M), f 0 = 0 →
        ∑ i, f (G i) = ∑ μ, f (K μ) := by
  classical
  refine ⟨Fintype.card ι, fun i => if h : (i : ℕ) < Fintype.card ι then
    K ((Fintype.equivFin ι).symm ⟨i, h⟩) else 0, ?_⟩
  intro M _ f hf
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg,
    not_false_iff, hf, add_zero, Fin.eta]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ fun i => rfl

/-- **Stinespring dilation, isometric form.**  Every completely positive trace preserving map
`Φ` on matrix algebras can be written as `Φ ρ = Tr_E (V ρ Vᴴ)` for an isometry
`V : ℂ^A → ℂ^B ⊗ ℂ^E`. -/
theorem stinespring_isometry (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hcp : IsCompletelyPositive Φ) (htp : IsTracePreserving Φ) :
    ∃ (k : ℕ) (V : Matrix (B × Fin (k + 1)) A ℂ),
      Vᴴ * V = 1 ∧ ∀ ρ : Matrix A A ℂ, Φ ρ = ptraceRight (V * ρ * Vᴴ) := by
  classical
  obtain ⟨K, hK⟩ := exists_kraus Φ hcp
  have hsum := kraus_sum_conjTranspose_mul_self K Φ htp hK
  obtain ⟨k, G, hG⟩ := exists_fin_reindex K
  have h1 : ∑ i : Fin (k + 1), (G i)ᴴ * G i = 1 := by
    rw [hG (fun X => Xᴴ * X) (by simp), hsum]
  have h2 : ∀ ρ : Matrix A A ℂ, ∑ i : Fin (k + 1), G i * ρ * (G i)ᴴ = Φ ρ := by
    intro ρ
    rw [hG (fun X => X * ρ * Xᴴ) (by simp), ← hK ρ]
  refine ⟨k, Matrix.of fun p a => G p.2 p.1 a, ?_, ?_⟩
  · ext a a'
    rw [← h1]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  · intro ρ
    ext b b'
    rw [← h2 ρ]
    simp only [ptraceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply]

/-- **Stinespring dilation, unitary form.**  Every CPTP map `Φ` on the matrix algebra of a
finite dimensional system `A` is the restriction of a unitary evolution on a larger system:
there are an environment `Fin k` with a pure reference state `e`, and a unitary `U` on
`A ⊗ Fin k`, such that `Φ ρ = Tr_E (U (ρ ⊗ |e⟩⟨e|) Uᴴ)` for all `ρ`. -/
theorem stinespring (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ)
    (hcp : IsCompletelyPositive Φ) (htp : IsTracePreserving Φ) :
    ∃ (k : ℕ) (e : Fin k) (U : Matrix (A × Fin k) (A × Fin k) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ ρ : Matrix A A ℂ,
        Φ ρ = ptraceRight (U * (ρ ⊗ₖ Matrix.single e e 1) * Uᴴ) := by
  classical
  obtain ⟨k, V, hV, hVtr⟩ := stinespring_isometry Φ hcp htp
  refine ⟨k + 1, ?_⟩
  set w : A → EuclideanSpace ℂ (A × Fin (k + 1)) :=
    fun a => WithLp.toLp 2 (fun p => V p a) with hw
  set s : Set (A × Fin (k + 1)) := {p | p.2 = 0} with hs
  set v : A × Fin (k + 1) → EuclideanSpace ℂ (A × Fin (k + 1)) := fun p => w p.1 with hv
  have hinner : ∀ a a' : A, inner ℂ (w a) (w a') = if a = a' then (1 : ℂ) else 0 := by
    intro a a'
    have h := congrArg (fun M => M a a') hV
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
    simpa [hw, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h
  have horth : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    simp only [Set.restrict_apply, hv]
    rw [hinner p.1 q.1]
    have h2 : p.2 = q.2 := by
      simp only [hs, Set.mem_setOf_eq] at hp hq
      rw [hp, hq]
    simp only [Subtype.mk.injEq, Prod.ext_iff, h2, and_true]
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (A × Fin (k + 1)))
      = Fintype.card (A × Fin (k + 1)) := by simp
  obtain ⟨bas, hbas⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hcol : ∀ (a : A) (x : A × Fin (k + 1)), (bas (a, 0)).ofLp x = V x a := fun a x => by
    rw [hbas (a, 0) (by simp [hs])]
  have hUU : (Matrix.of fun x y => (bas y).ofLp x :
        Matrix (A × Fin (k + 1)) (A × Fin (k + 1)) ℂ)ᴴ *
      (Matrix.of fun x y => (bas y).ofLp x) = 1 := by
    ext y y'
    have h := orthonormal_iff_ite.mp bas.orthonormal y y'
    simp only [PiLp.inner_apply, RCLike.inner_apply] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]; rfl
  refine ⟨0, Matrix.of fun x y => (bas y).ofLp x, hUU, mul_eq_one_comm.mp hUU, fun ρ => ?_⟩
  rw [hVtr ρ]
  congr 1
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, hcol]
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp [hcol]
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

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

