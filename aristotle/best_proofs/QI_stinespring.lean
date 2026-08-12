import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The partial trace over the second (ancilla) factor of a matrix indexed by a product. -/
noncomputable def ptraceRight {m E : Type} [Fintype E] (M : Matrix (m × E) (m × E) ℂ) :
    Matrix m m ℂ :=
  Matrix.of fun i j => ∑ e : E, M (i, e) (j, e)

/-- Amplification `id_k ⊗ Φ` of a linear map on matrices, acting blockwise. -/
noncomputable def ampl {n m : Type} (k : Type) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (M : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun a b => M (p.1, a) (q.1, b)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* if all its amplifications
`id_k ⊗ Φ` map positive semidefinite matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (k : Type) (_ : Fintype k) (M : Matrix (k × n) (k × n) ℂ),
    M.PosSemidef → (ampl k Φ M).PosSemidef

/-- A linear map between matrix algebras is *trace preserving* if it preserves the trace. -/
def IsTracePreserving (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ ρ : Matrix n n ℂ, (Φ ρ).trace = ρ.trace

omit [Fintype m] [DecidableEq m] in
/-- Expansion of a linear map on matrices in the standard basis. -/
lemma apply_eq_sum_single (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (ρ : Matrix n n ℂ)
    (i j : m) :
    Φ ρ i j = ∑ a : n, ∑ b : n, ρ a b * (Φ (Matrix.single a b 1)) i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (ρ a b) = (ρ a b) • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single]; simp, map_smul]
  simp

/-- The Choi matrix of `Φ`. -/
noncomputable def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix of a completely positive map is positive semidefinite. -/
lemma choi_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hCP : IsCompletelyPositive Φ) :
    (choi Φ).PosSemidef := by
  classical
  set B : Matrix Unit (n × n) ℂ := Matrix.of fun _ p => if p.1 = p.2 then 1 else 0 with hB
  have hcp := hCP n inferInstance (Bᴴ * B) (Matrix.posSemidef_conjTranspose_mul_self B)
  have heq : ampl n Φ (Bᴴ * B) = choi Φ := by
    ext p q
    have hblock : (Matrix.of fun a b => (Bᴴ * B) (p.1, a) (q.1, b))
        = Matrix.single p.1 q.1 (1 : ℂ) := by
      ext x y
      simp only [hB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul,
        Matrix.single, eq_comm]
      simp [ite_and]
      split_ifs <;> simp_all
    simp only [ampl, choi, Matrix.of_apply, hblock]
  rwa [heq] at hcp

/-- **Kraus decomposition**: a completely positive map admits a Kraus representation. -/
theorem kraus_decomposition {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hCP : IsCompletelyPositive Φ) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (K : E → Matrix m n ℂ),
      ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ e : E, K e * ρ * (K e)ᴴ := by
  classical
  have hC : (choi Φ).PosSemidef := choi_posSemidef hCP
  obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choi Φ = Bᴴ * B :=
    ⟨CFC.sqrt (choi Φ), by
      rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (choi Φ))).isHermitian.eq,
        CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC)]⟩
  have hCentry : ∀ (a b : n) (i j : m), Φ (Matrix.single a b 1) i j
      = ∑ e : n × m, (starRingEnd ℂ) (B e (a, i)) * B e (b, j) := by
    intro a b i j
    have := congrFun (congrFun hB (a, i)) (b, j)
    simpa [choi, Matrix.mul_apply, Matrix.conjTranspose_apply] using this
  refine ⟨n × m, inferInstance, inferInstance,
    fun e => Matrix.of fun (i : m) (a : n) => (starRingEnd ℂ) (B e (a, i)), ?_⟩
  intro ρ
  ext i j
  rw [apply_eq_sum_single Φ ρ i j]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    hCentry, Finset.mul_sum, Finset.sum_mul, RCLike.star_def, starRingEnd_self_apply]
  calc ∑ a : n, ∑ b : n, ∑ e : n × m,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j))
      = ∑ a : n, ∑ e : n × m, ∑ b : n,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ e : n × m, ∑ a : n, ∑ b : n,
        ρ a b * ((starRingEnd ℂ) (B e (a, i)) * B e (b, j)) := Finset.sum_comm
    _ = ∑ e : n × m, ∑ b : n, ∑ a : n,
        (starRingEnd ℂ) (B e (a, i)) * ρ a b * B e (b, j) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq m] in
/-- The Kraus operators of a trace preserving map satisfy the completeness relation. -/
lemma kraus_completeness {E : Type} [Fintype E] {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (K : E → Matrix m n ℂ) (hK : ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ e : E, K e * ρ * (K e)ᴴ)
    (hTP : IsTracePreserving Φ) :
    ∑ e : E, (K e)ᴴ * K e = 1 := by
  set A : Matrix n n ℂ := ∑ e : E, (K e)ᴴ * K e with hA
  have key : ∀ ρ : Matrix n n ℂ, (A * ρ).trace = ρ.trace := by
    intro ρ
    have h1 : (A * ρ).trace = ∑ e : E, (K e * ρ * (K e)ᴴ).trace := by
      rw [hA, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Matrix.trace_mul_comm (K e * ρ) ((K e)ᴴ), ← Matrix.mul_assoc]
    rw [h1, ← Matrix.trace_sum, ← hK ρ, hTP ρ]
  ext a b
  have h := key (Matrix.single b a 1)
  have h1 : (A * Matrix.single b a (1 : ℂ)).trace = A a b := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq]
  have h2 : (Matrix.single b a (1 : ℂ)).trace = if a = b then 1 else 0 := by
    simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  rw [h1, h2] at h
  rw [h, Matrix.one_apply]

/-- **Stinespring dilation, isometric form**: every CPTP map is the partial trace of a
conjugation by an isometry. -/
theorem stinespring_isometry {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (V : Matrix (m × E) n ℂ),
      Vᴴ * V = 1 ∧ ∀ ρ : Matrix n n ℂ, Φ ρ = ptraceRight (V * ρ * Vᴴ) := by
  obtain ⟨E, hEfin, hEdec, K, hK⟩ := kraus_decomposition hCP
  have hone : ∑ e : E, (K e)ᴴ * K e = 1 := kraus_completeness K hK hTP
  refine ⟨E, hEfin, hEdec, Matrix.of fun (p : m × E) (a : n) => K p.2 p.1 a, ?_, ?_⟩
  · ext a b
    rw [← hone]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  · intro ρ
    rw [hK ρ]
    ext i j
    simp [ptraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]

/-- **Stinespring dilation, unitary form**: every CPTP map `Φ` from `n × n` matrices to
`m × m` matrices dilates to a unitary `W` on the larger space `ℂⁿ ⊕ (ℂᵐ ⊗ ℂᴱ)`: the
block of `W` sending the input space into the output-plus-ancilla space is an isometry
`V`, and `Φ ρ` is obtained by conjugating `ρ` by `V` and tracing out the ancilla. -/
theorem stinespring {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E)
      (W : Matrix (n ⊕ m × E) (n ⊕ m × E) ℂ) (V : Matrix (m × E) n ℂ),
      W ∈ Matrix.unitaryGroup (n ⊕ m × E) ℂ ∧
      (∀ (p : m × E) (a : n), W (Sum.inr p) (Sum.inl a) = V p a) ∧
      Vᴴ * V = 1 ∧
      ∀ ρ : Matrix n n ℂ, Φ ρ = ptraceRight (V * ρ * Vᴴ) := by
  obtain ⟨E, hEfin, hEdec, V, hV, hΦ⟩ := stinespring_isometry hCP hTP
  refine ⟨E, hEfin, hEdec, Matrix.fromBlocks 0 Vᴴ V (1 - V * Vᴴ), V, ?_, ?_, hV, hΦ⟩
  · set W : Matrix (n ⊕ m × E) (n ⊕ m × E) ℂ := Matrix.fromBlocks 0 Vᴴ V (1 - V * Vᴴ) with hW
    have hherm : Wᴴ = W := by
      rw [hW, Matrix.fromBlocks_conjTranspose]; simp
    have hPP : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
    have e1 : (0 : Matrix n n ℂ) * 0 + Vᴴ * V = 1 := by rw [hV, Matrix.mul_zero, zero_add]
    have e2 : (0 : Matrix n n ℂ) * Vᴴ + Vᴴ * (1 - V * Vᴴ) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul,
        Matrix.zero_mul, sub_self, add_zero]
    have e3 : V * (0 : Matrix n n ℂ) + (1 - V * Vᴴ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one,
        Matrix.mul_zero, sub_self, add_zero]
    have e4 : V * Vᴴ + (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    have hsq : W * W = 1 := by
      rw [hW, Matrix.fromBlocks_multiply, e1, e2, e3, e4]
      exact Matrix.fromBlocks_one
    rw [Matrix.mem_unitaryGroup_iff, show star W = W from hherm]
    exact hsq
  · intro p a
    simp

/-! ### Non-vacuity: the identity channel is CPTP -/

lemma id_isCompletelyPositive {N : Type} [Fintype N] [DecidableEq N] :
    IsCompletelyPositive (LinearMap.id : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) := by
  intro k _ M hM
  have : ampl k (LinearMap.id : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) M = M := by
    ext p q; simp [ampl]
  rwa [this]

lemma id_isTracePreserving {N : Type} [Fintype N] [DecidableEq N] :
    IsTracePreserving (LinearMap.id : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) :=
  fun _ => rfl

end QI

#print axioms QI.stinespring

