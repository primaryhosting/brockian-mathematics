import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/

lemma relEnt_kronL_eq {δ : Type*} [Fintype δ] [DecidableEq δ]
    {R : Matrix (α × δ) (α × δ) ℂ} {Y : Matrix δ δ ℂ} (hY : Y.PosDef) :
    relEnt R ((1 : Matrix α α ℂ) ⊗ₖ Y) = -vnEnt R - ((ptL R) * CFC.log Y).trace.re := by
  have hK : CFC.log ((1 : Matrix α α ℂ) ⊗ₖ Y) = (1 : Matrix α α ℂ) ⊗ₖ CFC.log Y :=
    log_kronL hY
  rw [relEnt, hK, mul_sub, Matrix.trace_sub, Complex.sub_re, trace_mul_kronL, vnEnt]
  simp

lemma relEnt_kronL_self {δ : Type*} [Fintype δ] [DecidableEq δ]
    {R : Matrix (α × δ) (α × δ) ℂ} (hR : (ptL R).PosDef) :
    relEnt R ((1 : Matrix α α ℂ) ⊗ₖ (ptL R)) = -vnEnt R + vnEnt (ptL R) := by
  have h : vnEnt (ptL R) = -((ptL R * CFC.log (ptL R)).trace).re := by rw [vnEnt]; simp
  rw [relEnt_kronL_eq hR, h]
  ring

/-! ### The three marginals -/

/-- The reindexing `α × (β × γ) ≃ (α × β) × γ`. -/
def assocEquiv (α β γ : Type*) : (α × β × γ) ≃ ((α × β) × γ) := (Equiv.prodAssoc α β γ).symm

@[simp] lemma assocEquiv_symm_apply (p : (α × β) × γ) :
    (assocEquiv α β γ).symm p = (p.1.1, p.1.2, p.2) := rfl

/-- The marginal on `α ⊗ β`, obtained by tracing out the third factor. -/
noncomputable def ptC (M : Matrix (α × β × γ) (α × β × γ) ℂ) : Matrix (α × β) (α × β) ℂ :=
  ptR (M.submatrix (assocEquiv α β γ).symm (assocEquiv α β γ).symm)

/-- The marginal on `β ⊗ γ`, obtained by tracing out the first factor. -/
noncomputable def ptA (M : Matrix (α × β × γ) (α × β × γ) ℂ) : Matrix (β × γ) (β × γ) ℂ := ptL M

lemma ptC_posDef [Nonempty γ] {M : Matrix (α × β × γ) (α × β × γ) ℂ} (hM : M.PosDef) :
    (ptC M).PosDef :=
  ptR_posDef (PosDef.submatrix_equiv hM (assocEquiv α β γ))

lemma ptA_posDef [Nonempty α] {M : Matrix (α × β × γ) (α × β × γ) ℂ} (hM : M.PosDef) :
    (ptA M).PosDef := ptL_posDef hM

/-- The two ways of computing the marginal on `β` agree. -/
lemma ptL_ptC (M : Matrix (α × β × γ) (α × β × γ) ℂ) : ptL (ptC M) = ptR (ptA M) := by
  ext b b'
  simp only [ptL_apply, ptC, ptR_apply, ptA, Matrix.submatrix_apply, assocEquiv]
  exact Finset.sum_comm

/-- Tracing out the third factor of `1 ⊗ ρ_BC` gives `1 ⊗ ρ_B`. -/
lemma ptR_submatrix_kronL (N : Matrix (β × γ) (β × γ) ℂ) :
    ptR ((((1 : Matrix α α ℂ) ⊗ₖ N)).submatrix (assocEquiv α β γ).symm
        (assocEquiv α β γ).symm)
      = (1 : Matrix α α ℂ) ⊗ₖ (ptR N) := by
  ext p q
  simp only [ptR_apply, Matrix.submatrix_apply, assocEquiv_symm_apply,
    Matrix.kroneckerMap_apply]
  show ∑ x : γ, (1 : Matrix α α ℂ) p.1 q.1 * N (p.2, x) (q.2, x)
      = (1 : Matrix α α ℂ) p.1 q.1 * ∑ c, N (p.2, c) (q.2, c)
  rw [← Finset.mul_sum]

/-! ### The main theorem -/

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai).

For a positive definite matrix `ρ` on `α ⊗ β ⊗ γ`, with marginals `ρ_AB = Tr_γ ρ`,
`ρ_BC = Tr_α ρ` and `ρ_B = Tr_γ ρ_BC`, the von Neumann entropy `S(A) = -Tr (A log A)`
satisfies `S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.  (No normalisation of `ρ` is needed.) -/
theorem strong_subadditivity [Nonempty α] [Nonempty γ]
    {ρ : Matrix (α × β × γ) (α × β × γ) ℂ} (hρ : ρ.PosDef) :
    vnEnt ρ + vnEnt (ptR (ptA ρ)) ≤ vnEnt (ptC ρ) + vnEnt (ptA ρ) := by
  classical
  set e := assocEquiv α β γ with he
  set rBC : Matrix (β × γ) (β × γ) ℂ := ptA ρ with hrBC
  set rAB : Matrix (α × β) (α × β) ℂ := ptC ρ with hrAB
  set rB : Matrix β β ℂ := ptR rBC with hrB
  have hBC : rBC.PosDef := ptA_posDef hρ
  have hAB : rAB.PosDef := ptC_posDef hρ
  have hB : rB.PosDef := ptR_posDef hBC
  have hK : ((1 : Matrix α α ℂ) ⊗ₖ rBC).PosDef := Matrix.PosDef.one.kronecker hBC
  -- the partial trace of the reference state
  have hptK : ptR ((((1 : Matrix α α ℂ) ⊗ₖ rBC)).submatrix e.symm e.symm)
      = (1 : Matrix α α ℂ) ⊗ₖ rB := ptR_submatrix_kronL rBC
  have hptrho : ptR (ρ.submatrix e.symm e.symm) = rAB := rfl
  -- monotonicity of the relative entropy under tracing out the third factor
  have hmono := relEnt_ptR_le (PosDef.submatrix_equiv hρ e)
    (PosDef.submatrix_equiv hK e)
  rw [hptK, hptrho, relEnt_submatrix_equiv hρ hK e] at hmono
  -- identify both sides
  have hL : relEnt rAB ((1 : Matrix α α ℂ) ⊗ₖ rB) = -vnEnt rAB + vnEnt rB := by
    have hEq : ptL rAB = rB := by rw [hrAB, hrB, hrBC, ptL_ptC]
    rw [← hEq] at hB ⊢
    exact relEnt_kronL_self hB
  have hR : relEnt ρ ((1 : Matrix α α ℂ) ⊗ₖ rBC) = -vnEnt ρ + vnEnt rBC := by
    have hEq : ptL ρ = rBC := rfl
    rw [← hEq] at hBC ⊢
    exact relEnt_kronL_self hBC
  rw [hL, hR] at hmono
  linarith

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

import RequestProject.SSA.GeometricMean

/-!
# Iterated geometric means

`gpow m A B` is the `2⁻ᵐ`-weighted geometric mean of `A` and `B`, defined by iterating the
(balanced) geometric mean: `gpow 0 A B = B` and `gpow (m+1) A B = gmean A (gpow m A B)`.
For commuting `A`, `B` this is `A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ)`.

Since `gmean` is jointly concave and monotone in its second variable, each `gpow m` is
jointly concave.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The iterated geometric mean: `gpow m A B` is the `2⁻ᵐ`-weighted geometric mean. -/
noncomputable def gpow : ℕ → Matrix n n ℂ → Matrix n n ℂ → Matrix n n ℂ
  | 0, _, B => B
  | (m + 1), A, B => gmean A (gpow m A B)

@[simp] lemma gpow_zero (A B : Matrix n n ℂ) : gpow 0 A B = B := rfl

@[simp] lemma gpow_succ (m : ℕ) (A B : Matrix n n ℂ) :
    gpow (m + 1) A B = gmean A (gpow m A B) := rfl

variable {A B : Matrix n n ℂ}

lemma gpow_posSemidef (hA : A.PosDef) (hB : B.PosSemidef) (m : ℕ) : (gpow m A B).PosSemidef := by
  induction m with
  | zero => exact hB
  | succ m ih => exact gmean.posSemidef hA ih

lemma gpow_congr (hA : A.PosDef) (hB : B.PosSemidef) {T : Matrix n n ℂ} (hT : IsUnit T) (m : ℕ) :
    gpow m (T * A * Tᴴ) (T * B * Tᴴ) = T * gpow m A B * Tᴴ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [gpow_succ, ih, gpow_succ]
      exact gmean_congr hA (gpow_posSemidef hA hB m) hT

/-- Joint concavity of the iterated geometric mean. -/
theorem gpow_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) (m : ℕ) :
    ∑ i ∈ s, w i • gpow m (A i) (B i) ≤ gpow m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsum : (∑ i ∈ s, w i • gpow m (A i) (B i)).PosSemidef := by
        refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
          Matrix.PosSemidef.zero ?_
        intro i hi
        exact (gpow_posSemidef (hA i hi) (hB i hi) m).smul (by exact_mod_cast hw i hi)
      calc ∑ i ∈ s, w i • gpow (m + 1) (A i) (B i)
          = ∑ i ∈ s, w i • gmean (A i) (gpow m (A i) (B i)) := by simp
        _ ≤ gmean (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • gpow m (A i) (B i)) :=
            gmean_concave s w hw A (fun i => gpow m (A i) (B i)) hA
              (fun i hi => gpow_posSemidef (hA i hi) (hB i hi) m) hAsum
        _ ≤ gmean (∑ i ∈ s, w i • A i) (gpow m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i)) :=
            gmean_mono_right hAsum hsum ih
        _ = gpow (m + 1) (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by simp

/-- The scalar recursion corresponding to `gpow`: `dyseq m a b = a ^ (1 - 2⁻ᵐ) * b ^ (2⁻ᵐ)`. -/
noncomputable def dyseq : ℕ → ℝ → ℝ → ℝ
  | 0, _, b => b
  | (m + 1), a, b => Real.sqrt (a * dyseq m a b)

@[simp] lemma dyseq_zero (a b : ℝ) : dyseq 0 a b = b := rfl

@[simp] lemma dyseq_succ (m : ℕ) (a b : ℝ) :
    dyseq (m + 1) a b = Real.sqrt (a * dyseq m a b) := rfl

lemma dyseq_nonneg (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ dyseq m a b := by
  cases m with
  | zero => exact hb
  | succ m => exact Real.sqrt_nonneg _

lemma dyseq_pos (m : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < dyseq m a b := by
  induction m with
  | zero => exact hb
  | succ m ih => exact Real.sqrt_pos.2 (mul_pos ha ih)

/-- The closed form of the scalar recursion. -/
lemma dyseq_eq (m : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dyseq m a b = a ^ (1 - (2 : ℝ)⁻¹ ^ m) * b ^ ((2 : ℝ)⁻¹ ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [dyseq_succ, ih]
      set t : ℝ := (2:ℝ)⁻¹ ^ m with ht
      have htpos : 0 < t := by rw [ht]; positivity
      have h1 : a * (a ^ (1 - t) * b ^ t) = a ^ (2 - t) * b ^ t := by
        rw [show (2:ℝ) - t = 1 + (1 - t) by ring, Real.rpow_add ha, Real.rpow_one]
        ring
      have h2 : (2:ℝ)⁻¹ ^ (m+1) = t * (1/2) := by rw [ht, pow_succ]; ring
      rw [h1, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le, h2]
      congr 1
      congr 1
      ring

/-- `gpow` of diagonal matrices is diagonal, given by the scalar recursion. -/
lemma gpow_diagonal {a b : n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (m : ℕ) :
    gpow m (Matrix.diagonal fun i => (a i : ℂ)) (Matrix.diagonal fun i => (b i : ℂ))
      = Matrix.diagonal fun i => ((dyseq m (a i) (b i) : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [gpow_succ, ih]
      rw [gmean_diagonal ha (fun i => (dyseq_pos m (ha i) (hb i)).le)]
      rfl

end QI

import RequestProject.SSA.Invariance
import RequestProject.SSA.Convexity

/-!
# Partial traces

The partial trace over the right tensor factor, its basic properties, and the twirling
identities that express `Tr_γ M ⊗ 1` as an average of unitary conjugates of `M`.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The partial trace over the right tensor factor. -/
noncomputable def ptR (M : Matrix (β × γ) (β × γ) ℂ) : Matrix β β ℂ :=
  Matrix.of fun b b' => ∑ c, M (b, c) (b', c)

@[simp] lemma ptR_apply (M : Matrix (β × γ) (β × γ) ℂ) (b b' : β) :
    ptR M b b' = ∑ c, M (b, c) (b', c) := rfl

lemma ptR_add (M N : Matrix (β × γ) (β × γ) ℂ) : ptR (M + N) = ptR M + ptR N := by
  ext b b'; simp [Finset.sum_add_distrib]

lemma ptR_smul (w : ℝ) (M : Matrix (β × γ) (β × γ) ℂ) : ptR (w • M) = w • ptR M := by
  ext b b'; simp [Finset.smul_sum]

lemma ptR_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (M : ι → Matrix (β × γ) (β × γ) ℂ) :
    ptR (∑ i ∈ s, w i • M i) = ∑ i ∈ s, w i • ptR (M i) := by
  classical
  induction s using Finset.induction with
  | empty => ext b b'; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ptR_add, ptR_smul, ih]

lemma ptR_smul_one (t : ℝ) :
    ptR (t • (1 : Matrix (β × γ) (β × γ) ℂ)) = (t * Fintype.card γ) • (1 : Matrix β β ℂ) := by
  classical
  ext b b'
  by_cases h : b = b'
  · subst h
    simp [ptR, Matrix.one_apply, Complex.real_smul, Finset.card_univ, mul_comm]
  · simp [ptR, Matrix.one_apply, h, Complex.real_smul, Prod.ext_iff]

lemma trace_ptR (M : Matrix (β × γ) (β × γ) ℂ) : (ptR M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, ptR_apply, Fintype.sum_prod_type]

/-- The embedding of a vector on `β` into `β × γ` supported on the slice `c`. -/
private def sliceVec (x : β → ℂ) (c : γ) : β × γ → ℂ := fun p => if p.2 = c then x p.1 else 0

private lemma sliceVec_ne_zero {x : β → ℂ} (hx : x ≠ 0) (c : γ) : sliceVec x c ≠ 0 := by
  intro h
  apply hx
  funext b
  have := congrFun h (b, c)
  simpa [sliceVec] using this

private lemma dotProduct_sliceVec (M : Matrix (β × γ) (β × γ) ℂ) (x : β → ℂ) (c : γ) :
    star (sliceVec x c) ⬝ᵥ M *ᵥ (sliceVec x c)
      = ∑ b : β, ∑ b' : β, (starRingEnd ℂ) (x b) * (M (b, c) (b', c) * x b') := by
  simp [dotProduct, Matrix.mulVec, sliceVec, Fintype.sum_prod_type,
    apply_ite (starRingEnd ℂ), Finset.mul_sum]

private lemma dotProduct_ptR (M : Matrix (β × γ) (β × γ) ℂ) (x : β → ℂ) :
    star x ⬝ᵥ (ptR M) *ᵥ x = ∑ c, star (sliceVec x c) ⬝ᵥ M *ᵥ (sliceVec x c) := by
  classical
  have hL : star x ⬝ᵥ (ptR M) *ᵥ x = ∑ b : β, ∑ b' : β, ∑ c : γ,
      (starRingEnd ℂ) (x b) * (M (b, c) (b', c) * x b') := by
    simp [dotProduct, Matrix.mulVec, ptR, Finset.mul_sum, Finset.sum_mul]
  rw [hL, Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => dotProduct_sliceVec M x c)]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => Finset.sum_comm)]
  exact Finset.sum_comm

lemma ptR_isHermitian {M : Matrix (β × γ) (β × γ) ℂ} (hM : M.IsHermitian) :
    (ptR M).IsHermitian := by
  ext b b'
  simp only [Matrix.conjTranspose_apply, ptR_apply]
  rw [star_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := congrFun (congrFun hM (b, c)) (b', c)
  simpa [Matrix.conjTranspose_apply] using this

lemma ptR_posSemidef {M : Matrix (β × γ) (β × γ) ℂ} (hM : M.PosSemidef) : (ptR M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨ptR_isHermitian hM.1, fun x => ?_⟩
  rw [dotProduct_ptR]
  exact Finset.sum_nonneg fun c _ => (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 _

lemma ptR_posDef [Nonempty γ] {M : Matrix (β × γ) (β × γ) ℂ} (hM : M.PosDef) : (ptR M).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨ptR_isHermitian hM.1, fun x hx => ?_⟩
  rw [dotProduct_ptR]
  refine Finset.sum_pos' (fun c _ => ?_) ?_
  · exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM.posSemidef).2 _
  · obtain ⟨c₀⟩ := ‹Nonempty γ›
    exact ⟨c₀, Finset.mem_univ _,
      (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 (sliceVec_ne_zero hx c₀)⟩

/-! ### The partial trace over the left factor -/

/-- The partial trace over the left tensor factor. -/
noncomputable def ptL (M : Matrix (β × γ) (β × γ) ℂ) : Matrix γ γ ℂ :=
  Matrix.of fun c c' => ∑ b, M (b, c) (b, c')

@[simp] lemma ptL_apply (M : Matrix (β × γ) (β × γ) ℂ) (c c' : γ) :
    ptL M c c' = ∑ b, M (b, c) (b, c') := rfl

lemma ptL_eq_ptR (M : Matrix (β × γ) (β × γ) ℂ) :
    ptL M = ptR (M.submatrix (Equiv.prodComm β γ).symm (Equiv.prodComm β γ).symm) := by
  ext c c'
  simp [ptL, ptR]

lemma ptL_add (M N : Matrix (β × γ) (β × γ) ℂ) : ptL (M + N) = ptL M + ptL N := by
  ext c c'; simp [Finset.sum_add_distrib]

lemma ptL_smul (w : ℝ) (M : Matrix (β × γ) (β × γ) ℂ) : ptL (w • M) = w • ptL M := by
  ext c c'; simp [Finset.smul_sum]

lemma ptL_smul_one (t : ℝ) :
    ptL (t • (1 : Matrix (β × γ) (β × γ) ℂ)) = (t * Fintype.card β) • (1 : Matrix γ γ ℂ) := by
  classical
  ext c c'
  by_cases h : c = c'
  · subst h
    simp [ptL, Matrix.one_apply, Complex.real_smul, Finset.card_univ, mul_comm]
  · simp [ptL, Matrix.one_apply, h, Complex.real_smul, Prod.ext_iff]

lemma ptL_posDef [Nonempty β] {M : Matrix (β × γ) (β × γ) ℂ} (hM : M.PosDef) :
    (ptL M).PosDef := by
  rw [ptL_eq_ptR]
  exact ptR_posDef (PosDef.submatrix_equiv hM (Equiv.prodComm β γ))

/-- The trace of a product with `1 ⊗ Z` only sees the partial trace over the left factor. -/
lemma trace_mul_kronL (M : Matrix (β × γ) (β × γ) ℂ) (Z : Matrix γ γ ℂ) :
    (M * ((1 : Matrix β β ℂ) ⊗ₖ Z)).trace = ((ptL M) * Z).trace := by
  classical
  have hL : (M * ((1 : Matrix β β ℂ) ⊗ₖ Z)).trace
      = ∑ d : γ, ∑ d' : γ, ∑ a : β, M (a, d) (a, d') * Z d' d := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      one_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have key : ∀ a : β, (∑ a' : β, ∑ d' : γ, (if a' = a then M (a, d) (a', d') * Z d' d else 0))
        = ∑ d' : γ, M (a, d) (a, d') * Z d' d := by
      intro a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d' _ => ?_
      simp
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => key a)]
    exact Finset.sum_comm
  have hR : ((ptL M) * Z).trace = ∑ d : γ, ∑ d' : γ, ∑ a : β, M (a, d) (a, d') * Z d' d := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ptL, Matrix.of_apply,
      Finset.sum_mul]
  rw [hL, hR]

/-! ### Stage 1 of the twirl: averaging over sign flips -/

/-- The `±1` valued character attached to a subset of `γ`. -/
noncomputable def sgnC (s : γ → Bool) (c : γ) : ℂ := if s c then 1 else -1

lemma sgnC_mul_self (s : γ → Bool) (c : γ) : sgnC s c * sgnC s c = 1 := by
  unfold sgnC; by_cases h : s c <;> simp [h]

lemma star_sgnC (s : γ → Bool) (c : γ) : star (sgnC s c) = sgnC s c := by
  unfold sgnC; by_cases h : s c <;> simp [h]

/-- Flipping the value of a `Bool`-valued function at one point. -/
def flipAt (x : γ) : (γ → Bool) ≃ (γ → Bool) where
  toFun s := Function.update s x (!s x)
  invFun s := Function.update s x (!s x)
  left_inv s := by
    funext y
    by_cases h : y = x
    · subst h; simp
    · simp [Function.update_of_ne h]
  right_inv s := by
    funext y
    by_cases h : y = x
    · subst h; simp
    · simp [Function.update_of_ne h]

lemma sum_sgnC (x y : γ) :
    ∑ s : γ → Bool, sgnC s x * sgnC s y
      = if x = y then ((2 : ℂ) ^ Fintype.card γ) else 0 := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · simp only [if_pos rfl]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => sgnC_mul_self s x)]
    simp [Finset.card_univ, Fintype.card_fun]
  · rw [if_neg hxy]
    set T : ℂ := ∑ s : γ → Bool, sgnC s x * sgnC s y with hT
    have hstep : ∀ s : γ → Bool,
        sgnC (flipAt x s) x * sgnC (flipAt x s) y = -(sgnC s x * sgnC s y) := by
      intro s
      have h1 : sgnC (flipAt x s) x = -(sgnC s x) := by
        show (if (Function.update s x (!s x)) x then (1 : ℂ) else -1) = _
        rw [Function.update_self]
        unfold sgnC
        by_cases h : s x <;> simp [h]
      have h2 : sgnC (flipAt x s) y = sgnC s y := by
        show (if (Function.update s x (!s x)) y then (1 : ℂ) else -1) = _
        rw [Function.update_of_ne (Ne.symm hxy)]
        rfl
      rw [h1, h2]; ring
    have h3 : T = ∑ s : γ → Bool, sgnC (flipAt x s) x * sgnC (flipAt x s) y :=
      (Equiv.sum_comp (flipAt x) (fun s => sgnC s x * sgnC s y)).symm
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hstep s)] at h3
    rw [Finset.sum_neg_distrib, ← hT] at h3
    linear_combination h3 / 2

/-- The diagonal sign unitary attached to `s`. -/
noncomputable def Dsign (β : Type*) [Fintype β] [DecidableEq β] (s : γ → Bool) :
    Matrix (β × γ) (β × γ) ℂ := diagonal (fun p => sgnC s p.2)

lemma Dsign_star (s : γ → Bool) : star (Dsign β s) = Dsign β s := by
  show (Dsign β s)ᴴ = Dsign β s
  rw [Dsign, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  exact star_sgnC s p.2

lemma Dsign_mem_unitary (s : γ → Bool) : Dsign β s ∈ unitary (Matrix (β × γ) (β × γ) ℂ) := by
  have hsq : Dsign β s * Dsign β s = 1 := by
    rw [Dsign, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext p
    exact sgnC_mul_self s p.2
  constructor <;> rw [Dsign_star] <;> exact hsq

lemma Dsign_conj_apply (s : γ → Bool) (M : Matrix (β × γ) (β × γ) ℂ) (p q : β × γ) :
    (Dsign β s * M * star (Dsign β s)) p q = sgnC s p.2 * sgnC s q.2 * M p q := by
  rw [Dsign_star, Dsign, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- The pinching of `M` that kills the off-diagonal blocks in the `γ` factor. -/
noncomputable def pinch (M : Matrix (β × γ) (β × γ) ℂ) : Matrix (β × γ) (β × γ) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then M p q else 0

lemma sum_Dsign_conj (M : Matrix (β × γ) (β × γ) ℂ) :
    ∑ s : γ → Bool, (((2 : ℝ) ^ Fintype.card γ)⁻¹ • (Dsign β s * M * star (Dsign β s)))
      = pinch M := by
  classical
  ext p q
  rw [Matrix.sum_apply]
  have hterm : ∀ s : γ → Bool,
      (((2 : ℝ) ^ Fintype.card γ)⁻¹ • (Dsign β s * M * star (Dsign β s))) p q
        = (((2 : ℂ) ^ Fintype.card γ)⁻¹ * M p q) * (sgnC s p.2 * sgnC s q.2) := by
    intro s
    rw [Matrix.smul_apply, Dsign_conj_apply]
    push_cast [Complex.real_smul]
    ring
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hterm s), ← Finset.mul_sum,
    sum_sgnC]
  have h2 : ((2 : ℂ) ^ Fintype.card γ) ≠ 0 := by positivity
  by_cases h : p.2 = q.2
  · rw [if_pos h]
    field_simp
    simp [pinch, h]
  · rw [if_neg h, mul_zero]
    simp [pinch, h]

/-! ### Stage 2 of the twirl: averaging over cyclic shifts -/

section Rot

variable [Nonempty γ]

instance neZeroCardOfNonempty : NeZero (Fintype.card γ) := ⟨Fintype.card_ne_zero⟩

/-- An identification of `γ` with the cyclic group of its own cardinality. -/
noncomputable def enum (γ : Type*) [Fintype γ] [DecidableEq γ] [Nonempty γ] :
    γ ≃ ZMod (Fintype.card γ) :=
  Fintype.equivOfCardEq (by simp)

/-- The cyclic shift permutation of `γ`. -/
noncomputable def rotPerm (k : ZMod (Fintype.card γ)) : Equiv.Perm γ :=
  (enum γ).trans ((Equiv.addRight k).trans (enum γ).symm)

/-- The cyclic shift acting on the second tensor factor. -/
noncomputable def rotEquiv (β : Type*) (k : ZMod (Fintype.card γ)) : (β × γ) ≃ (β × γ) :=
  Equiv.prodCongr (Equiv.refl β) (rotPerm k)

lemma rotEquiv_symm_apply (k : ZMod (Fintype.card γ)) (p : β × γ) :
    (rotEquiv β k).symm p = (p.1, (rotPerm k).symm p.2) := rfl

lemma sum_rotPerm {A : Type*} [AddCommMonoid A] (f : γ → A) (c : γ) :
    ∑ k : ZMod (Fintype.card γ), f ((rotPerm k).symm c) = ∑ e : γ, f e := by
  refine Fintype.sum_equiv ((Equiv.subLeft (enum γ c)).trans (enum γ).symm) _ _ ?_
  intro k
  congr 1
  simp [rotPerm, sub_eq_add_neg]

lemma sum_rot_pinch (M : Matrix (β × γ) (β × γ) ℂ) :
    ∑ k : ZMod (Fintype.card γ),
        (pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm
      = (ptR M) ⊗ₖ (1 : Matrix γ γ ℂ) := by
  classical
  ext p q
  rw [Matrix.sum_apply]
  by_cases hcc : p.2 = q.2
  · have hterm : ∀ k : ZMod (Fintype.card γ),
        ((pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm) p q
          = M (p.1, (rotPerm k).symm p.2) (q.1, (rotPerm k).symm p.2) := by
      intro k
      rw [Matrix.submatrix_apply, rotEquiv_symm_apply, rotEquiv_symm_apply, ← hcc]
      simp [pinch]
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    rw [sum_rotPerm (fun e => M (p.1, e) (q.1, e)) p.2]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hcc]
  · have hterm : ∀ k : ZMod (Fintype.card γ),
        ((pinch M).submatrix (rotEquiv β k).symm (rotEquiv β k).symm) p q = 0 := by
      intro k
      rw [Matrix.submatrix_apply, rotEquiv_symm_apply, rotEquiv_symm_apply]
      simp only [pinch, Matrix.of_apply, ite_eq_right_iff]
      intro hEq
      exact absurd ((rotPerm k).symm.injective hEq) hcc
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hcc]

/-! ### Monotonicity of the relative entropy under the partial trace -/

lemma pinch_posDef {R : Matrix (β × γ) (β × γ) ℂ} (hR : R.PosDef) : (pinch R).PosDef := by
  rw [← sum_Dsign_conj R]
  refine posDef_weighted_sum Finset.univ ⟨fun _ => true, Finset.mem_univ _⟩ _
    (fun i _ => by positivity) _ (fun s _ => ?_)
  exact PosDef.conj_unitary hR ⟨Dsign β s, Dsign_mem_unitary s⟩

/-- **Monotonicity of the relative entropy under the partial trace**. -/
theorem relEnt_ptR_le {R S : Matrix (β × γ) (β × γ) ℂ} (hR : R.PosDef) (hS : S.PosDef) :
    relEnt (ptR R) (ptR S) ≤ relEnt R S := by
  classical
  have hcardBool : Fintype.card (γ → Bool) = 2 ^ Fintype.card γ := by
    simp [Fintype.card_fun]
  have hpR := pinch_posDef hR
  have hpS := pinch_posDef hS
  -- Stage 1: pinching decreases the relative entropy.
  have step1 : relEnt (pinch R) (pinch S) ≤ relEnt R S := by
    have h := relEnt_convex (ι := γ → Bool) Finset.univ
      (fun _ => ((2 : ℝ) ^ Fintype.card γ)⁻¹) (fun i _ => by positivity)
      (fun s => Dsign β s * R * star (Dsign β s))
      (fun s => Dsign β s * S * star (Dsign β s))
      (fun s _ => PosDef.conj_unitary hR ⟨Dsign β s, Dsign_mem_unitary s⟩)
      (fun s _ => PosDef.conj_unitary hS ⟨Dsign β s, Dsign_mem_unitary s⟩)
      (by rw [sum_Dsign_conj]; exact hpR) (by rw [sum_Dsign_conj]; exact hpS)
    rw [sum_Dsign_conj, sum_Dsign_conj] at h
    have hrhs : ∑ s : γ → Bool, ((2 : ℝ) ^ Fintype.card γ)⁻¹ *
        relEnt (Dsign β s * R * star (Dsign β s)) (Dsign β s * S * star (Dsign β s))
          = relEnt R S := by
      have hcongr : ∀ s : γ → Bool,
          ((2 : ℝ) ^ Fintype.card γ)⁻¹ *
            relEnt (Dsign β s * R * star (Dsign β s)) (Dsign β s * S * star (Dsign β s))
            = ((2 : ℝ) ^ Fintype.card γ)⁻¹ * relEnt R S := by
        intro s
        rw [relEnt_conj_unitary hR hS ⟨Dsign β s, Dsign_mem_unitary s⟩]
      rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hcongr s), Finset.sum_const,
        Finset.card_univ, hcardBool, nsmul_eq_mul]
      have h2 : ((2 : ℝ) ^ Fintype.card γ) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [hrhs] at h
    exact h
  -- Stage 2: averaging over cyclic shifts.
  have step2 : relEnt ((ptR R) ⊗ₖ (1 : Matrix γ γ ℂ)) ((ptR S) ⊗ₖ (1 : Matrix γ γ ℂ))
      ≤ (Fintype.card γ : ℝ) * relEnt (pinch R) (pinch S) := by
    have hsumR : ∑ k : ZMod (Fintype.card γ), (1 : ℝ) •
        ((pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = (ptR R) ⊗ₖ (1 : Matrix γ γ ℂ) := by
      simpa using sum_rot_pinch (β := β) R
    have hsumS : ∑ k : ZMod (Fintype.card γ), (1 : ℝ) •
        ((pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = (ptR S) ⊗ₖ (1 : Matrix γ γ ℂ) := by
      simpa using sum_rot_pinch (β := β) S
    have h := relEnt_convex (ι := ZMod (Fintype.card γ)) Finset.univ (fun _ => (1 : ℝ))
      (fun i _ => zero_le_one)
      (fun k => (pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
      (fun k => (pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
      (fun k _ => PosDef.submatrix_equiv hpR (rotEquiv β k))
      (fun k _ => PosDef.submatrix_equiv hpS (rotEquiv β k))
      (by rw [hsumR]; exact (ptR_posDef hR).kronecker Matrix.PosDef.one)
      (by rw [hsumS]; exact (ptR_posDef hS).kronecker Matrix.PosDef.one)
    rw [hsumR, hsumS] at h
    refine le_trans h (le_of_eq ?_)
    have hcongr : ∀ k : ZMod (Fintype.card γ), (1 : ℝ) *
        relEnt ((pinch R).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          ((pinch S).submatrix (rotEquiv β k).symm (rotEquiv β k).symm)
          = relEnt (pinch R) (pinch S) := by
      intro k
      rw [one_mul, relEnt_submatrix_equiv hpR hpS]
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hcongr k), Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [relEnt_kronR (m := γ) (ptR_posDef hR) (ptR_posDef hS)] at step2
  have hd : (0 : ℝ) < (Fintype.card γ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have := le_trans step2 (by
    exact mul_le_mul_of_nonneg_left step1 hd.le :
      (Fintype.card γ : ℝ) * relEnt (pinch R) (pinch S)
        ≤ (Fintype.card γ : ℝ) * relEnt R S)
  exact le_of_mul_le_mul_left this hd

end Rot

end QI

import RequestProject.SSA.Setup

/-!
# The operator geometric mean

For `A` positive definite and `B` positive semidefinite we define
`gmean A B = A ^ (1/2) * (A ^ (-1/2) * B * A ^ (-1/2)) ^ (1/2) * A ^ (1/2)`, characterised
by `X * A⁻¹ * X = B`, and prove the facts we need:

* `gmean.eq_of`: uniqueness,
* `le_gmean`: maximality among hermitian `X` with `X * A⁻¹ * X ≤ B`,
* `gmean_mono_right`: monotonicity in the second variable,
* `gmean_concave`: joint concavity (Ando's theorem).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

section Basic

/-- Positive definite matrices are invertible as ring elements. -/
lemma posDef_isUnit {A : Matrix n n ℂ} (hA : A.PosDef) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 (ne_of_gt hA.det_pos))

lemma posDef_mul_inv {A : Matrix n n ℂ} (hA : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).1 (posDef_isUnit hA))

lemma posDef_inv_mul {A : Matrix n n ℂ} (hA : A.PosDef) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).1 (posDef_isUnit hA))

/-- Conjugation by a hermitian matrix is monotone. -/
lemma conj_le_conj {X Y : Matrix n n ℂ} (h : X ≤ Y) {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T * X * T ≤ T * Y * T := by
  have := conjugate_le_conjugate h T
  rwa [star_eq_conjTranspose, hT.eq] at this

end Basic

variable {A B : Matrix n n ℂ}

/-- The square root of a positive definite matrix is positive definite. -/
lemma sqrt_posDef (hA : A.PosDef) : (CFC.sqrt A).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.1
    (Matrix.isStrictlyPositive_iff_posDef.2 hA).sqrt

lemma sqrt_hermitian (A : Matrix n n ℂ) : (CFC.sqrt A).IsHermitian :=
  (CFC.sqrt_nonneg A).posSemidef.1

/-- The operator geometric mean of `A` (positive definite) and `B` (positive semidefinite). -/
noncomputable def gmean (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹) * CFC.sqrt A

namespace gmean

variable (hA : A.PosDef) (hB : B.PosSemidef)
include hA

lemma sqrt_mul_sqrt : CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

lemma inv_sqrt_posDef : ((CFC.sqrt A)⁻¹).PosDef := (sqrt_posDef hA).inv

lemma inv_sqrt_herm : ((CFC.sqrt A)⁻¹).IsHermitian := (inv_sqrt_posDef hA).1

lemma inv_eq : A⁻¹ = (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ := by
  conv_lhs => rw [← sqrt_mul_sqrt hA]
  rw [Matrix.mul_inv_rev]

lemma sqrt_mul_inv : CFC.sqrt A * (CFC.sqrt A)⁻¹ = 1 := posDef_mul_inv (sqrt_posDef hA)

lemma inv_mul_sqrt : (CFC.sqrt A)⁻¹ * CFC.sqrt A = 1 := posDef_inv_mul (sqrt_posDef hA)

/-- Conjugating by `sqrt A` undoes conjugating by its inverse. -/
lemma conj_sqrt_conj_inv (X : Matrix n n ℂ) :
    CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A = X := by
  calc CFC.sqrt A * ((CFC.sqrt A)⁻¹ * X * (CFC.sqrt A)⁻¹) * CFC.sqrt A
      = (CFC.sqrt A * (CFC.sqrt A)⁻¹) * X * ((CFC.sqrt A)⁻¹ * CFC.sqrt A) := by noncomm_ring
    _ = X := by rw [sqrt_mul_inv hA, inv_mul_sqrt hA, one_mul, mul_one]

include hB

lemma inner_posSemidef : ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹).PosSemidef := by
  have := hB.conjTranspose_mul_mul_same ((CFC.sqrt A)⁻¹)
  rwa [(inv_sqrt_herm hA).eq] at this

lemma posSemidef : (gmean A B).PosSemidef := by
  have h2 : (CFC.sqrt ((CFC.sqrt A)⁻¹ * B * (CFC.sqrt A)⁻¹)).PosSemidef :=
    (CFC.sqrt_nonneg _).posSemidef
  have := h2.conjTranspose_mul_mul_same (CFC.sqrt A)
  rwa [(sqrt_hermitian A).eq] at this

lemma hermitian : (gmean A B).IsHermitian := (posSemidef hA hB).1

/-- The defining property of the geometric mean. -/
lemma mul_inv_mul : gmean A B * A⁻¹ * gmean A B = B := by
  set S := CFC.sqrt A with hS
  set C := CFC.sqrt (S⁻¹ * B * S⁻¹) with hC
  have hCC : C * C = S⁻¹ * B * S⁻¹ :=
    CFC.sqrt_mul_sqrt_self _ (inner_posSemidef hA hB).nonneg
  show (S * C * S) * A⁻¹ * (S * C * S) = B
  rw [inv_eq hA]
  calc (S * C * S) * (S⁻¹ * S⁻¹) * (S * C * S)
      = S * C * ((S * S⁻¹) * (S⁻¹ * S)) * C * S := by noncomm_ring
    _ = S * (C * C) * S := by
        rw [sqrt_mul_inv hA, inv_mul_sqrt hA]; noncomm_ring
    _ = S * (S⁻¹ * B * S⁻¹) * S := by rw [hCC]
    _ = B := conj_sqrt_conj_inv hA B

omit hB in
/-- Uniqueness: the geometric mean is the unique positive semidefinite solution of
`X * A⁻¹ * X = B`. -/
lemma eq_of {X : Matrix n n ℂ} (hX : X.PosSemidef) (h : X * A⁻¹ * X = B) : gmean A B = X := by
  set S := CFC.sqrt A with hS
  have hXY : (S⁻¹ * X * S⁻¹).PosSemidef := by
    have := hX.conjTranspose_mul_mul_same (S⁻¹)
    rwa [(inv_sqrt_herm hA).eq] at this
  have key : (S⁻¹ * X * S⁻¹) * (S⁻¹ * X * S⁻¹) = S⁻¹ * B * S⁻¹ := by
    rw [← h, inv_eq hA]; noncomm_ring
  have hsq : CFC.sqrt (S⁻¹ * B * S⁻¹) = S⁻¹ * X * S⁻¹ := by
    rw [CFC.sqrt_eq_iff _ _ ?_ hXY.nonneg]
    · exact key
    · rw [← key]
      have : ((S⁻¹ * X * S⁻¹) * (S⁻¹ * X * S⁻¹)).PosSemidef := by
        have h1 := Matrix.posSemidef_conjTranspose_mul_self (S⁻¹ * X * S⁻¹)
        rwa [hXY.1.eq] at h1
      exact this.nonneg
  show S * CFC.sqrt (S⁻¹ * B * S⁻¹) * S = X
  rw [hsq]
  exact conj_sqrt_conj_inv hA X

end gmean

/-- Maximality of the geometric mean. -/
lemma le_gmean (hA : A.PosDef) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (h : X * A⁻¹ * X ≤ B) : X ≤ gmean A B := by
  set S := CFC.sqrt A with hS
  have hSherm : S.IsHermitian := sqrt_hermitian A
  have hSi : (S⁻¹).IsHermitian := gmean.inv_sqrt_herm hA
  set Y := S⁻¹ * X * S⁻¹ with hY
  have hYherm : Y.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hY]
    simp [Matrix.conjTranspose_mul, hX.eq, hSi.eq, Matrix.mul_assoc]
  have hYY : Y * Y = S⁻¹ * (X * A⁻¹ * X) * S⁻¹ := by
    rw [hY, gmean.inv_eq hA]; noncomm_ring
  have hle : Y * Y ≤ S⁻¹ * B * S⁻¹ := by
    rw [hYY]; exact conj_le_conj h hSi
  have habs : CFC.abs Y = CFC.sqrt (Y * Y) := by
    rw [CFC.abs, star_eq_conjTranspose, hYherm.eq]
  have h1 : Y ≤ CFC.abs Y := by
    rw [← sub_nonneg, CFC.abs_sub_self Y hYherm]
    exact nsmul_nonneg (CFC.negPart_nonneg Y) 2
  have h2 : CFC.sqrt (Y * Y) ≤ CFC.sqrt (S⁻¹ * B * S⁻¹) := CFC.monotone_sqrt hle
  have hYle : Y ≤ CFC.sqrt (S⁻¹ * B * S⁻¹) := le_trans h1 (habs ▸ h2)
  have hcon := conj_le_conj hYle hSherm
  rw [hY, gmean.conj_sqrt_conj_inv hA X] at hcon
  exact hcon

/-- Monotonicity of the geometric mean in its second argument. -/
lemma gmean_mono_right (hA : A.PosDef) (hB : B.PosSemidef) {B' : Matrix n n ℂ} (h : B ≤ B') :
    gmean A B ≤ gmean A B' :=
  le_gmean hA (gmean.hermitian hA hB) (by rw [gmean.mul_inv_mul hA hB]; exact h)

section Blocks

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Positive semidefiniteness of a `2 × 2` block matrix with hermitian off-diagonal blocks. -/
lemma fromBlocks_posSemidef_iff (hA : A.PosDef) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (Matrix.fromBlocks A X X B).PosSemidef ↔ X * A⁻¹ * X ≤ B := by
  letI := (posDef_isUnit hA).invertible
  have h := Matrix.PosDef.fromBlocks₁₁ (R' := ℂ) X B hA
  rw [hX.eq] at h
  rw [h, Matrix.le_iff]

lemma fromBlocks_sum {ι : Type*} (s : Finset ι) (f g h k : ι → Matrix n n ℂ) :
    Matrix.fromBlocks (∑ i ∈ s, f i) (∑ i ∈ s, g i) (∑ i ∈ s, h i) (∑ i ∈ s, k i)
      = ∑ i ∈ s, Matrix.fromBlocks (f i) (g i) (h i) (k i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.fromBlocks_zero]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, ← ih, Matrix.fromBlocks_add]

end Blocks

/-- **Joint concavity of the operator geometric mean** (Ando's theorem), in the form of a
finite weighted sum. -/
theorem gmean_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) :
    ∑ i ∈ s, w i • gmean (A i) (B i) ≤ gmean (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  set X := ∑ i ∈ s, w i • gmean (A i) (B i) with hXdef
  have hXpsd : X.PosSemidef := by
    rw [hXdef]
    refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero ?_
    intro i hi
    exact (gmean.posSemidef (hA i hi) (hB i hi)).smul (by exact_mod_cast hw i hi)
  have hXherm : X.IsHermitian := hXpsd.1
  refine le_gmean hAsum hXherm ?_
  rw [← fromBlocks_posSemidef_iff hAsum hXherm]
  have : Matrix.fromBlocks (∑ i ∈ s, w i • A i) X X (∑ i ∈ s, w i • B i)
      = ∑ i ∈ s, w i • Matrix.fromBlocks (A i) (gmean (A i) (B i)) (gmean (A i) (B i)) (B i) := by
    rw [hXdef]
    simp only [Matrix.fromBlocks_smul]
    exact fromBlocks_sum s _ _ _ _
  rw [this]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero ?_
  intro i hi
  refine Matrix.PosSemidef.smul ?_ (by exact_mod_cast hw i hi)
  rw [fromBlocks_posSemidef_iff (hA i hi) (gmean.hermitian (hA i hi) (hB i hi))]
  rw [gmean.mul_inv_mul (hA i hi) (hB i hi)]

/-- Covariance of the geometric mean under congruence by an invertible matrix. -/
lemma gmean_congr (hA : A.PosDef) (hB : B.PosSemidef) {T : Matrix n n ℂ} (hT : IsUnit T) :
    gmean (T * A * Tᴴ) (T * B * Tᴴ) = T * gmean A B * Tᴴ := by
  have hTH : IsUnit (Tᴴ) := hT.star
  have hTinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det T).1 hT)
  have hTinv' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det T).1 hT)
  have hTHinv : Tᴴ * (Tᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hTH)
  have hTHinv' : (Tᴴ)⁻¹ * Tᴴ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hTH)
  have hApos : (T * A * Tᴴ).PosDef := by
    rw [show (Tᴴ : Matrix n n ℂ) = star T from rfl]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hT).2 hA
  refine gmean.eq_of hApos ?_ ?_
  · have := (gmean.posSemidef hA hB).conjTranspose_mul_mul_same (Tᴴ)
    simpa [Matrix.mul_assoc] using this
  · have hinv : (T * A * Tᴴ)⁻¹ = (Tᴴ)⁻¹ * A⁻¹ * T⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [hinv]
    calc T * gmean A B * Tᴴ * ((Tᴴ)⁻¹ * A⁻¹ * T⁻¹) * (T * gmean A B * Tᴴ)
        = T * gmean A B * ((Tᴴ * (Tᴴ)⁻¹) * A⁻¹ * (T⁻¹ * T)) * gmean A B * Tᴴ := by noncomm_ring
      _ = T * (gmean A B * A⁻¹ * gmean A B) * Tᴴ := by
          rw [hTHinv, hTinv']; noncomm_ring
      _ = T * B * Tᴴ := by rw [gmean.mul_inv_mul hA hB]

/-- The geometric mean of two diagonal matrices. -/
lemma gmean_diagonal {a b : n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i) :
    gmean (Matrix.diagonal fun i => (a i : ℂ)) (Matrix.diagonal fun i => (b i : ℂ))
      = Matrix.diagonal fun i => ((Real.sqrt (a i * b i) : ℝ) : ℂ) := by
  have hApos : (Matrix.diagonal fun i => (a i : ℂ)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast ha i
  refine gmean.eq_of hApos ?_ ?_
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have : (0:ℝ) ≤ Real.sqrt (a i * b i) := Real.sqrt_nonneg _
    exact_mod_cast this
  · have hai : ∀ i, (a i : ℂ) ≠ 0 := by
      intro i
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (ha i)
    have hdinv : (Matrix.diagonal fun i => (a i : ℂ))⁻¹
        = Matrix.diagonal fun i => ((a i : ℂ))⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hai i)
    rw [hdinv, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : (Real.sqrt (a i * b i) : ℂ) * (Real.sqrt (a i * b i) : ℂ)
        = ((a i * b i : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_nonneg (ha i).le (hb i))]
    calc (Real.sqrt (a i * b i) : ℂ) * ((a i : ℂ))⁻¹ * (Real.sqrt (a i * b i) : ℂ)
        = ((Real.sqrt (a i * b i) : ℂ) * (Real.sqrt (a i * b i) : ℂ)) * ((a i : ℂ))⁻¹ := by
          ring
      _ = ((a i * b i : ℝ) : ℂ) * ((a i : ℂ))⁻¹ := by rw [hsq]
      _ = (b i : ℂ) := by
          push_cast
          rw [mul_comm ((a i : ℂ)) ((b i : ℂ)), mul_assoc, mul_inv_cancel₀ (hai i), mul_one]

end QI

import RequestProject.SSA.Spectral

/-!
# Von Neumann entropy and relative entropy

`vnEnt A = -Tr (A log A)` and `relEnt A B = Tr (A (log A - log B))`, together with their
spectral formulas and Klein's inequality.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

/-- Von Neumann entropy `-Tr (A log A)`. -/
noncomputable def vnEnt (A : Matrix n n ℂ) : ℝ := (-(A * CFC.log A).trace).re

/-- Umegaki relative entropy `Tr (A (log A - log B))`. -/
noncomputable def relEnt (A B : Matrix n n ℂ) : ℝ := ((A * (CFC.log A - CFC.log B)).trace).re

lemma trace_mul_log (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * CFC.log B).trace
      = ∑ i, ∑ j, ((hA.eigenvalues i * Real.log (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ) := by
  have hid : cfc (id : ℝ → ℝ) A = A := cfc_id ℝ A hA
  have := trace_cfc_mul_cfc hA hB id Real.log
  rw [hid] at this
  rw [show CFC.log B = cfc Real.log B from rfl]
  exact this

lemma trace_mul_log_self (hA : A.IsHermitian) :
    (A * CFC.log A).trace = ∑ i, ((hA.eigenvalues i * Real.log (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [trace_mul_log hA hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [ovl_self hA i i]
    simp
  · intro j _ hj
    rw [ovl_self hA i j, if_neg (Ne.symm hj)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The spectral formula for the von Neumann entropy. -/
lemma vnEnt_eq (hA : A.IsHermitian) : vnEnt A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  rw [vnEnt, trace_mul_log_self hA, ← Complex.ofReal_sum]
  simp only [← Complex.ofReal_neg, Complex.ofReal_re]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog]; ring

/-- The spectral formula for the relative entropy. -/
lemma relEnt_eq (hA : A.IsHermitian) (hB : B.IsHermitian) :
    relEnt A B = ∑ i, ∑ j, ovl hA hB i j *
      (hA.eigenvalues i * (Real.log (hA.eigenvalues i) - Real.log (hB.eigenvalues j))) := by
  have hsplit : A * (CFC.log A - CFC.log B) = A * CFC.log A - A * CFC.log B := by
    rw [mul_sub]
  rw [relEnt, hsplit, Matrix.trace_sub, trace_mul_log_self hA, trace_mul_log hA hB]
  rw [← Complex.ofReal_sum]
  have h2 : (∑ i, ∑ j, ((hA.eigenvalues i * Real.log (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ))
      = ((∑ i, ∑ j, hA.eigenvalues i * Real.log (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have h3 : ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i)
      = ∑ i, ∑ j, ovl hA hB i j * (hA.eigenvalues i * Real.log (hA.eigenvalues i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ovl_sum_right hA hB i, one_mul]
  rw [h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The scalar inequality behind Klein's inequality. -/
lemma scalar_klein {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  rcases eq_or_lt_of_le hx with h | hx'
  · simp [← h]
    linarith
  · have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx')] at h1
    have h2 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
      mul_le_mul_of_nonneg_left h1 hx
    have h3 : x * (y / x - 1) = y - x := by field_simp
    rw [h3] at h2
    nlinarith [h2]

/-- **Klein's inequality**. -/
theorem klein (hA : A.PosSemidef) (hB : B.PosDef) :
    A.trace.re - B.trace.re ≤ relEnt A B := by
  rw [relEnt_eq hA.1 hB.1]
  have htA : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  have htB : B.trace.re = ∑ j, hB.1.eigenvalues j := by
    rw [hB.1.trace_eq_sum_eigenvalues]
    simp
  rw [htA, htB]
  have hlow : ∀ i, ∑ j, ovl hA.1 hB.1 i j *
      (hA.1.eigenvalues i - hB.1.eigenvalues j) ≤ ∑ j, ovl hA.1 hB.1 i j *
      (hA.1.eigenvalues i * (Real.log (hA.1.eigenvalues i) - Real.log (hB.1.eigenvalues j))) := by
    intro i
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left
      (scalar_klein (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j)) (ovl_nonneg hA.1 hB.1 i j)
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => hlow i)
  have hexp : ∀ i, ∑ j, ovl hA.1 hB.1 i j * (hA.1.eigenvalues i - hB.1.eigenvalues j)
      = hA.1.eigenvalues i - ∑ j, ovl hA.1 hB.1 i j * hB.1.eigenvalues j := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => mul_sub (ovl hA.1 hB.1 i j) (hA.1.eigenvalues i)
      (hB.1.eigenvalues j))]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ovl_sum_right hA.1 hB.1 i, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib]
  have hswap : ∑ i, ∑ j, ovl hA.1 hB.1 i j * hB.1.eigenvalues j = ∑ j, hB.1.eigenvalues j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ovl_sum_left hA.1 hB.1 j, one_mul]
  rw [hswap]

end QI

import RequestProject.SSA.Setup

/-!
# Spectral formulas for traces of functional calculi

For hermitian matrices `A`, `B` with eigenvalues `λ i`, `μ j` and eigenvector unitaries `U`, `V`,
we have `Tr (f A * g B) = ∑ i j, f (λ i) * g (μ j) * c i j` with `c i j = |(U* V) i j|²`
a doubly stochastic matrix of overlaps.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

section trace

lemma trace_diagonal_conj (W : Matrix n n ℂ) (d e : n → ℝ) :
    (diagonal (fun i => (d i : ℂ)) * W * diagonal (fun j => (e j : ℂ)) * Wᴴ).trace
      = ∑ i, ∑ j, ((d i * e j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  have step : ∀ i : n, ((diagonal (fun i => (d i : ℂ)) * W * diagonal (fun j => (e j : ℂ)) * Wᴴ))
      i i = ∑ j, ((d i * e j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [Matrix.diagonal_mul, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.star_def]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun i _ => step i

/-- Trace of a product of two conjugated diagonal matrices. -/
lemma trace_conj_diag_pair (U V : Matrix n n ℂ) (d e : n → ℝ) :
    ((U * diagonal (fun i => (d i : ℂ)) * star U) *
        (V * diagonal (fun j => (e j : ℂ)) * star V)).trace
      = ∑ i, ∑ j, ((d i * e j * Complex.normSq ((star U * V) i j) : ℝ) : ℂ) := by
  set Df : Matrix n n ℂ := diagonal (fun i => (d i : ℂ))
  set Dg : Matrix n n ℂ := diagonal (fun j => (e j : ℂ))
  have hWH : (star U * V : Matrix n n ℂ)ᴴ = star V * U := by
    simp [star_eq_conjTranspose, Matrix.conjTranspose_mul]
  have e1 : (U * Df * star U * (V * Dg * star V)) = (U * Df * star U * V * Dg) * star V := by
    noncomm_ring
  have e2 : ((U * Df * star U * (V * Dg * star V))).trace
      = (Df * (star U * V) * Dg * (star V * U)).trace := by
    rw [e1, Matrix.trace_mul_comm, Matrix.trace_mul_comm (Df * (star U * V) * Dg)]
    congr 1
    noncomm_ring
  rw [e2, ← hWH, trace_diagonal_conj]

end trace

variable {A B : Matrix n n ℂ}

/-- The overlap matrix between the eigenbases of two hermitian matrices; it is doubly
stochastic. -/
noncomputable def ovl (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq
    (((star hA.eigenvectorUnitary : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)) i j)

lemma ovl_nonneg (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : 0 ≤ ovl hA hB i j :=
  Complex.normSq_nonneg _

private lemma unitary_row_sum (W : Matrix n n ℂ) (hW : W * Wᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => M i i) hW
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Complex.star_def]
    ring
  exact_mod_cast this

private lemma unitary_col_sum (W : Matrix n n ℂ) (hW : Wᴴ * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => M j j) hW
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Complex.star_def]
  exact_mod_cast this

/-- The overlap matrix `W = U* V` of two eigenbases is unitary. -/
lemma ovl_unitary (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((star hA.eigenvectorUnitary : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)) ∈
      unitary (Matrix n n ℂ) :=
  mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2

lemma ovl_sum_right (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, ovl hA hB i j = 1 := by
  refine unitary_row_sum _ ?_ i
  have := (ovl_unitary hA hB).2
  simpa [star_eq_conjTranspose] using this

lemma ovl_sum_left (hA : A.IsHermitian) (hB : B.IsHermitian) (j : n) :
    ∑ i, ovl hA hB i j = 1 := by
  refine unitary_col_sum _ ?_ j
  have := (ovl_unitary hA hB).1
  simpa [star_eq_conjTranspose] using this

/-- The overlap matrix of a hermitian matrix with itself is the identity. -/
lemma ovl_self (hA : A.IsHermitian) (i j : n) :
    ovl hA hA i j = if i = j then 1 else 0 := by
  have h : ((star hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)) = 1 := by
    simpa using (ovl_unitary hA hA).1
  rw [ovl, h]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

/-- **The master spectral formula**: the trace of a product of two functional calculi. -/
theorem trace_cfc_mul_cfc (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace
      = ∑ i, ∑ j, ((f (hA.eigenvalues i) * g (hB.eigenvalues j) * ovl hA hB i j : ℝ) : ℂ) := by
  classical
  set U : Matrix n n ℂ := ↑hA.eigenvectorUnitary with hUdef
  set V : Matrix n n ℂ := ↑hB.eigenvectorUnitary with hVdef
  set W : Matrix n n ℂ := star U * V with hWdef
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hVV : V * star V = 1 := Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2
  have hcfcA : cfc f A = U * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) * star U := by
    rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
    rfl
  have hcfcB : cfc g B = V * diagonal (fun j => ((g (hB.eigenvalues j) : ℝ) : ℂ)) * star V := by
    rw [hB.cfc_eq g, Matrix.IsHermitian.cfc]
    rfl
  rw [hcfcA, hcfcB, trace_conj_diag_pair]
  rfl

end QI

import RequestProject.SSA.Entropy

/-!
# Continuity of the von Neumann entropy

`vnEnt A = Tr (negMulLog A)` for hermitian `A`, and `negMulLog` is continuous on all of `ℝ`,
so the von Neumann entropy is continuous on hermitian matrices.  This is what allows the
strong subadditivity inequality to be extended from positive definite matrices to arbitrary
positive semidefinite ones.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Matrix Filter

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a functional calculus is the sum of the values on the eigenvalues. -/
lemma trace_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  have hcfcA : cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [hA.cfc_eq f, Matrix.IsHermitian.cfc]
    rfl
  rw [hcfcA, Matrix.trace_mul_comm, ← mul_assoc,
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]

lemma vnEnt_eq_trace_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    vnEnt A = (cfc Real.negMulLog A).trace.re := by
  rw [vnEnt_eq hA, trace_cfc hA, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma spectrum_subset_Icc [Nonempty n] {A : Matrix n n ℂ} {r : ℝ} (h : ‖A‖ ≤ r) :
    spectrum ℝ A ⊆ Set.Icc (-r) r := by
  intro x hx
  have h1 := spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hx
  rw [Real.norm_eq_abs] at h1
  exact ⟨(abs_le.1 (h1.trans h)).1, (abs_le.1 (h1.trans h)).2⟩

/-- **Continuity of the von Neumann entropy** on hermitian matrices. -/
theorem tendsto_vnEnt {X : Type*} {l : Filter X} {F : X → Matrix n n ℂ} {A : Matrix n n ℂ}
    (hF : ∀ x, (F x).IsHermitian) (hA : A.IsHermitian) (h : Tendsto F l (𝓝 A)) :
    Tendsto (fun x => vnEnt (F x)) l (𝓝 (vnEnt A)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hzero : ∀ M : Matrix n n ℂ, vnEnt M = 0 := by
      intro M; rw [vnEnt]; simp
    simp only [hzero]
    exact tendsto_const_nhds
  · set r : ℝ := ‖A‖ + 1 with hr
    have hcomp : IsCompact (Set.Icc (-r) r) := isCompact_Icc
    have hnorm : Tendsto (fun x => ‖F x‖) l (𝓝 ‖A‖) := h.norm
    have hev : ∀ᶠ x in l, spectrum ℝ (F x) ⊆ Set.Icc (-r) r := by
      have hlt : ∀ᶠ x in l, ‖F x‖ < ‖A‖ + 1 := hnorm.eventually_lt_const (by linarith)
      filter_upwards [hlt] with x hx
      exact spectrum_subset_Icc hx.le
    have hspecA : spectrum ℝ A ⊆ Set.Icc (-r) r := spectrum_subset_Icc (by simp [hr])
    have hcfc := Filter.Tendsto.cfc (𝕜 := ℝ) hcomp Real.negMulLog h hev
      (Filter.Eventually.of_forall (fun x => (hF x : IsSelfAdjoint (F x))))
      hspecA (hA : IsSelfAdjoint A) Real.continuous_negMulLog.continuousOn
    have hcont : Continuous (fun M : Matrix n n ℂ => M.trace.re) := by fun_prop
    have hres := (hcont.continuousAt (x := cfc Real.negMulLog A)).tendsto.comp hcfc
    rw [vnEnt_eq_trace_cfc hA]
    refine hres.congr fun x => ?_
    rw [vnEnt_eq_trace_cfc (hF x)]
    rfl

end QI

import RequestProject.SSA.Entropy

/-!
# Star algebra homomorphisms of matrix algebras

Conjugation by a unitary, reindexing along an equivalence, and the two Kronecker embeddings
`X ↦ X ⊗ 1`, `Y ↦ 1 ⊗ Y` are unital star algebra homomorphisms, hence commute with the
continuous functional calculus.  This gives the transformation rules for `CFC.log` that are
needed to manipulate relative entropies.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Conjugation by a unitary -/

/-- Conjugation by a unitary, as a star algebra homomorphism. -/
noncomputable def conjHom (u : unitary (Matrix n n ℂ)) :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := (u : Matrix n n ℂ) * M * star (u : Matrix n n ℂ)
  map_one' := by rw [mul_one, u.2.2]
  map_mul' x y := by
    have h : star (u : Matrix n n ℂ) * (u : Matrix n n ℂ) = 1 := u.2.1
    calc (u : Matrix n n ℂ) * (x * y) * star (u : Matrix n n ℂ)
        = (u : Matrix n n ℂ) * x * (star (u : Matrix n n ℂ) * u) * y *
            star (u : Matrix n n ℂ) := by rw [h]; simp [mul_assoc]
      _ = ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)) *
            ((u : Matrix n n ℂ) * y * star (u : Matrix n n ℂ)) := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, mul_one, u.2.2]
  map_star' x := by simp only [StarMul.star_mul, star_star, mul_assoc]

lemma conjHom_apply (u : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    conjHom u M = (u : Matrix n n ℂ) * M * star (u : Matrix n n ℂ) := rfl

lemma conjHom_continuous (u : unitary (Matrix n n ℂ)) : Continuous (conjHom u) :=
  LinearMap.continuous_of_finiteDimensional (conjHom u).toLinearMap

lemma cfc_conj (u : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A)) :
    (u : Matrix n n ℂ) * cfc f A * star (u : Matrix n n ℂ)
      = cfc f ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (conjHom u) f A hf (conjHom_continuous u) hA

/-! ### Reindexing -/

/-- Reindexing a matrix along an equivalence, as a star algebra homomorphism. -/
def reindHom (e : n ≃ m) : Matrix n n ℂ →⋆ₐ[ℂ] Matrix m m ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_one' := Matrix.submatrix_one_equiv e.symm
  map_mul' x y := (Matrix.submatrix_mul_equiv x y _ _ _).symm
  map_zero' := rfl
  map_add' x y := rfl
  commutes' r := by
    ext i j
    simp [Matrix.submatrix_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' x := rfl

lemma reindHom_apply (e : n ≃ m) (M : Matrix n n ℂ) :
    reindHom e M = M.submatrix e.symm e.symm := rfl

lemma reindHom_continuous (e : n ≃ m) : Continuous (reindHom e) :=
  LinearMap.continuous_of_finiteDimensional (reindHom e).toLinearMap

lemma cfc_reind (e : n ≃ m) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A)) :
    (cfc f A).submatrix e.symm e.symm = cfc f (A.submatrix e.symm e.symm) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (reindHom e) f A hf (reindHom_continuous e) hA

/-! ### Kronecker embeddings -/

/-- `X ↦ X ⊗ 1`, as a star algebra homomorphism. -/
def kronHomR (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix m m ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' x y := Matrix.add_kronecker x y 1
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]
  map_star' x := by simp [star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

/-- `Y ↦ 1 ⊗ Y`, as a star algebra homomorphism. -/
def kronHomL (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun M := (1 : Matrix n n ℂ) ⊗ₖ M
  map_one' := Matrix.one_kronecker_one
  map_mul' x y := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' x y := Matrix.kronecker_add 1 x y
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul]
  map_star' x := by simp [star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

lemma kronHomR_continuous : Continuous (kronHomR n m) :=
  LinearMap.continuous_of_finiteDimensional (kronHomR n m).toLinearMap

lemma cfc_kronR {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    (cfc f A) ⊗ₖ (1 : Matrix m m ℂ) = cfc f (A ⊗ₖ (1 : Matrix m m ℂ)) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (kronHomR n m) f A hf kronHomR_continuous hA

lemma kronHomL_continuous : Continuous (kronHomL n m) :=
  LinearMap.continuous_of_finiteDimensional (kronHomL n m).toLinearMap

lemma cfc_kronL {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    (1 : Matrix n n ℂ) ⊗ₖ cfc f A = cfc f ((1 : Matrix n n ℂ) ⊗ₖ A) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (kronHomL n m) f A hf kronHomL_continuous hA

end QI

import Mathlib

/-!
# Setup for the strong subadditivity development

Basic instances and helper lemmas about positive matrices, used throughout.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrices over `ℂ` form a C⋆-algebra (with the ℓ²-operator norm). -/
noncomputable instance matrixCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where

end QI

import RequestProject.SSA.Dyadic
import RequestProject.SSA.Entropy

/-!
# The Kronecker lift and joint convexity of relative entropy

Multiplication operators `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ Bᵀ` commute, so the iterated geometric
means of the lifted pair compute `Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))`.  Joint concavity of the
geometric mean therefore gives joint concavity of these trace functionals, and letting
`m → ∞` yields the joint convexity of the relative entropy.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The quadratic form at the "vectorised identity" -/

/-- The vectorised identity matrix. -/
def vecOne (n : Type*) [DecidableEq n] : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0

/-- The quadratic form of the vectorised identity. -/
noncomputable def qform (M : Matrix (n × n) (n × n) ℂ) : ℂ := ∑ i, ∑ j, M (i, i) (j, j)

lemma qform_eq_dotProduct (M : Matrix (n × n) (n × n) ℂ) :
    qform M = star (vecOne n) ⬝ᵥ (M *ᵥ vecOne n) := by
  classical
  simp [qform, dotProduct, Matrix.mulVec, vecOne, Fintype.sum_prod_type, mul_ite, ite_mul]

lemma qform_nonneg {M : Matrix (n × n) (n × n) ℂ} (hM : M.PosSemidef) : 0 ≤ (qform M).re := by
  rw [qform_eq_dotProduct]
  exact (Complex.le_def.1 ((Matrix.posSemidef_iff_dotProduct_mulVec.1 hM).2 _)).1

lemma qform_add (M N : Matrix (n × n) (n × n) ℂ) : qform (M + N) = qform M + qform N := by
  simp [qform, Finset.sum_add_distrib]

lemma qform_smul (w : ℝ) (M : Matrix (n × n) (n × n) ℂ) : qform (w • M) = (w : ℂ) * qform M := by
  simp [qform, Finset.mul_sum, Complex.real_smul]

lemma qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (n × n) (n × n) ℂ) :
    qform (∑ i ∈ s, f i) = ∑ i ∈ s, qform (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert a s ha ih => rw [Finset.sum_insert ha, qform_add, ih, Finset.sum_insert ha]

lemma qform_mono {M N : Matrix (n × n) (n × n) ℂ} (h : M ≤ N) : (qform M).re ≤ (qform N).re := by
  have hpsd : (N - M).PosSemidef := h
  have := qform_nonneg hpsd
  rw [show N - M = N + (-1 : ℝ) • M by module, qform_add, qform_smul] at this
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at this
  norm_num at this
  linarith [this]

lemma qform_conj_diagonal (W : Matrix (n × n) (n × n) ℂ) (d : n × n → ℝ) :
    qform (W * diagonal (fun p => (d p : ℂ)) * Wᴴ)
      = ((∑ p : n × n, d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
  have step : ∀ i j : n, (W * diagonal (fun p => (d p : ℂ)) * Wᴴ) (i, i) (j, j)
      = ∑ p : n × n, (d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p) := by
    intro i j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Complex.star_def]
    ring
  have key : ∀ p : n × n, ∑ i, ∑ j, ((d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p))
      = ((d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
    intro p
    calc ∑ i, ∑ j, ((d p : ℂ) * W (i, i) p * (starRingEnd ℂ) (W (j, j) p))
        = ∑ i, ((d p : ℂ) * W (i, i) p * ∑ j, (starRingEnd ℂ) (W (j, j) p)) := by
          simp [Finset.mul_sum]
      _ = (∑ i, (d p : ℂ) * W (i, i) p) * (∑ j, (starRingEnd ℂ) (W (j, j) p)) := by
          rw [Finset.sum_mul]
      _ = (d p : ℂ) * ((∑ i, W (i, i) p) * (starRingEnd ℂ) (∑ j, W (j, j) p)) := by
          rw [← Finset.mul_sum, map_sum]; ring
      _ = ((d p * Complex.normSq (∑ k, W (k, k) p) : ℝ) : ℂ) := by
          push_cast
          rw [Complex.normSq_eq_conj_mul_self]
          ring
  simp only [qform]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step i j))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_comm, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun p _ => key p

/-! ### The lifted multiplication operators -/

/-- Left multiplication by `A`, as a matrix acting on vectorised matrices. -/
noncomputable def liftL (A : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := A ⊗ₖ (1 : Matrix n n ℂ)

/-- Right multiplication by `B`, as a matrix acting on vectorised matrices. -/
noncomputable def liftR (B : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := (1 : Matrix n n ℂ) ⊗ₖ Bᵀ

variable {A B : Matrix n n ℂ}

lemma liftL_posDef (hA : A.PosDef) : (liftL A).PosDef := hA.kronecker Matrix.PosDef.one

lemma liftR_posSemidef (hB : B.PosSemidef) : (liftR B).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hB.transpose

lemma liftL_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (A : ι → Matrix n n ℂ) :
    liftL (∑ i ∈ s, w i • A i) = ∑ i ∈ s, w i • liftL (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [liftL]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, liftL, liftL,
        Matrix.add_kronecker, Matrix.smul_kronecker]
      rfl

lemma liftR_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (B : ι → Matrix n n ℂ) :
    liftR (∑ i ∈ s, w i • B i) = ∑ i ∈ s, w i • liftR (B i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [liftR]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, liftR, liftR,
        Matrix.transpose_add, Matrix.kronecker_add, Matrix.transpose_smul,
        Matrix.kronecker_smul]
      rfl

/-- `Qd m A B = Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))`, defined through the geometric mean of the
lifted multiplication operators. -/
noncomputable def Qd (m : ℕ) (A B : Matrix n n ℂ) : ℝ :=
  (qform (gpow m (liftL A) (liftR B))).re

/-- **Joint concavity** of `(A, B) ↦ Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))`. -/
theorem Qd_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (A B : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAsum : (∑ i ∈ s, w i • A i).PosDef) (m : ℕ) :
    ∑ i ∈ s, w i * Qd m (A i) (B i) ≤ Qd m (∑ i ∈ s, w i • A i) (∑ i ∈ s, w i • B i) := by
  have hlift : (∑ i ∈ s, w i • liftL (A i)).PosDef := by
    rw [← liftL_sum]
    exact liftL_posDef hAsum
  have h := gpow_concave s w hw (fun i => liftL (A i)) (fun i => liftR (B i))
    (fun i hi => liftL_posDef (hA i hi)) (fun i hi => liftR_posSemidef (hB i hi)) hlift m
  have hmono := qform_mono h
  rw [qform_sum] at hmono
  simp only [qform_smul] at hmono
  rw [Complex.re_sum] at hmono
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hmono
  rw [← liftL_sum, ← liftR_sum] at hmono
  exact hmono

/-- **Spectral evaluation** of `Qd`. -/
theorem Qd_eval (hA : A.PosDef) (hB : B.PosDef) (m : ℕ) :
    Qd m A B
      = ∑ i, ∑ j, ovl hA.1 hB.1 i j * dyseq m (hA.1.eigenvalues i) (hB.1.eigenvalues j) := by
  classical
  set U : Matrix n n ℂ := ↑hA.1.eigenvectorUnitary with hUdef
  set V : Matrix n n ℂ := ↑hB.1.eigenvectorUnitary with hVdef
  set lam := hA.1.eigenvalues with hlam
  set mu := hB.1.eigenvalues with hmu
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hA.1.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hB.1.eigenvectorUnitary.2
  set Vc : Matrix n n ℂ := (Vᴴ)ᵀ with hVcdef
  have hVcH : Vcᴴ = Vᵀ := by
    ext i j
    simp [hVcdef, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hVcVt : Vc * Vᵀ = 1 := by
    rw [hVcdef, ← Matrix.transpose_mul, hVV, Matrix.transpose_one]
  set W : Matrix (n × n) (n × n) ℂ := U ⊗ₖ Vc with hWdef
  have hWH : Wᴴ = Uᴴ ⊗ₖ Vᵀ := by rw [hWdef, Matrix.conjTranspose_kronecker, hVcH]
  have hWW : W * Wᴴ = 1 := by
    rw [hWH, hWdef, ← Matrix.mul_kronecker_mul, hUU, hVcVt, Matrix.one_kronecker_one]
  have hWunit : IsUnit W :=
    (Matrix.isUnit_iff_isUnit_det W).2 (Matrix.isUnit_det_of_right_inverse hWW)
  -- spectral decompositions
  have hspecA : A = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  have hspecB : B = V * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.1.spectral_theorem]
    rfl
  set dl : n × n → ℝ := fun p => lam p.1 with hdl
  set dr : n × n → ℝ := fun p => mu p.2 with hdr
  have hDl : (diagonal fun p => ((dl p : ℝ) : ℂ))
      = (diagonal fun i => ((lam i : ℝ) : ℂ)) ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp [hdl]
  have hDr : (diagonal fun p => ((dr p : ℝ) : ℂ))
      = (1 : Matrix n n ℂ) ⊗ₖ (diagonal fun j => ((mu j : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp [hdr]
  have hL : liftL A = W * (diagonal fun p => ((dl p : ℝ) : ℂ)) * Wᴴ := by
    have h : W * (diagonal fun p => ((dl p : ℝ) : ℂ)) * Wᴴ
        = (U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ) ⊗ₖ (Vc * 1 * Vᵀ) := by
      rw [hWdef, hWH, hDl, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [h, mul_one, hVcVt, ← hspecA]
    rfl
  have hR : liftR B = W * (diagonal fun p => ((dr p : ℝ) : ℂ)) * Wᴴ := by
    have h : W * (diagonal fun p => ((dr p : ℝ) : ℂ)) * Wᴴ
        = (U * 1 * Uᴴ) ⊗ₖ (Vc * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᵀ) := by
      rw [hWdef, hWH, hDr, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    have hBt : Vc * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᵀ = Bᵀ := by
      conv_rhs => rw [hspecB]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, hVcdef]
      rw [Matrix.mul_assoc]
    rw [h, mul_one, hUU, hBt]
    rfl
  -- positivity of the diagonal data
  have hdlpos : ∀ p, 0 < dl p := fun p => hA.eigenvalues_pos p.1
  have hdrpos : ∀ p, 0 < dr p := fun p => hB.eigenvalues_pos p.2
  have hDlpos : (diagonal fun p => ((dl p : ℝ) : ℂ)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro p
    exact_mod_cast hdlpos p
  have hDrpsd : (diagonal fun p => ((dr p : ℝ) : ℂ)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro p
    exact_mod_cast (hdrpos p).le
  have hgpow : gpow m (liftL A) (liftR B)
      = W * (diagonal fun p => ((dyseq m (dl p) (dr p) : ℝ) : ℂ)) * Wᴴ := by
    rw [hL, hR, gpow_congr hDlpos hDrpsd hWunit m, gpow_diagonal hdlpos hdrpos m]
  -- evaluate the quadratic form
  have hnormSq : ∀ i j : n, Complex.normSq (∑ k, W (k, k) (i, j)) = ovl hA.1 hB.1 i j := by
    intro i j
    have hentry : ∀ k : n, W (k, k) (i, j) = U k i * (starRingEnd ℂ) (V k j) := by
      intro k
      simp [hWdef, hVcdef, Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have hsum : (∑ k, W (k, k) (i, j))
        = (starRingEnd ℂ) (((star U : Matrix n n ℂ) * V) i j) := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hentry k]
      simp [star_eq_conjTranspose, Matrix.conjTranspose_apply, mul_comm]
    rw [hsum, Complex.normSq_conj]
    rfl
  rw [Qd, hgpow, qform_conj_diagonal, Complex.ofReal_re, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hnormSq i j]
  ring

end QI

import RequestProject.SSA.Homs

/-!
# Invariance properties of the relative entropy

The relative entropy is unchanged by conjugation with a unitary and by reindexing the matrix
along an equivalence of index types.  We also record how `CFC.log` interacts with the
embedding `Y ↦ 1 ⊗ Y`.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The real logarithm is continuous on the spectrum of a positive definite matrix. -/
lemma continuousOn_log_spectrum {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn Real.log (spectrum ℝ A) := by
  refine Real.continuousOn_log.mono ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  refine hx ?_
  rw [resolventSet]
  simpa using hA.isUnit

/-! ### Positive definiteness of weighted sums -/

omit [DecidableEq n] in
lemma dotProduct_weighted_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (A : ι → Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (∑ i ∈ s, w i • A i) *ᵥ x = ∑ i ∈ s, (w i : ℂ) * (star x ⬝ᵥ A i *ᵥ x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, dotProduct_add, ih]
      congr 1
      rw [Matrix.smul_mulVec, dotProduct_smul]
      simp [Complex.real_smul]

lemma posDef_weighted_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (A : ι → Matrix n n ℂ) (hA : ∀ i ∈ s, (A i).PosDef) :
    (∑ i ∈ s, w i • A i).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · show (∑ i ∈ s, w i • A i)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.conjTranspose_smul, (hA i hi).1]
    simp
  · intro x hx
    rw [dotProduct_weighted_sum]
    refine Finset.sum_pos' (fun i hi => ?_) ?_
    · exact le_of_lt (mul_pos (by exact_mod_cast hw i hi)
        ((Matrix.posDef_iff_dotProduct_mulVec.mp (hA i hi)).2 hx))
    · obtain ⟨i, hi⟩ := hs
      exact ⟨i, hi, mul_pos (by exact_mod_cast hw i hi)
        ((Matrix.posDef_iff_dotProduct_mulVec.mp (hA i hi)).2 hx)⟩

/-! ### Reindexing -/

lemma PosDef.submatrix_equiv {M : Matrix n n ℂ} (h : M.PosDef) (e : n ≃ m) :
    (M.submatrix e.symm e.symm).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨h.1.submatrix _, ?_⟩
  intro x hx
  have key : star x ⬝ᵥ (M.submatrix e.symm e.symm) *ᵥ x
      = star (x ∘ e) ⬝ᵥ M *ᵥ (x ∘ e) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply,
      Function.comp_apply]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · simp
    · rw [← Equiv.sum_comp e.symm]
      simp
  rw [key]
  refine (Matrix.posDef_iff_dotProduct_mulVec.mp h).2 ?_
  intro hc
  apply hx
  funext i
  simpa using congrFun hc (e.symm i)

lemma trace_submatrix_equiv (M : Matrix n n ℂ) (e : n ≃ m) :
    (M.submatrix e.symm e.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)

lemma log_submatrix_equiv {A : Matrix n n ℂ} (hA : A.PosDef) (e : n ≃ m) :
    CFC.log (A.submatrix e.symm e.symm) = (CFC.log A).submatrix e.symm e.symm :=
  (cfc_reind e hA.1 Real.log (continuousOn_log_spectrum hA)).symm

/-- The relative entropy is invariant under reindexing. -/
theorem relEnt_submatrix_equiv {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (e : n ≃ m) :
    relEnt (A.submatrix e.symm e.symm) (B.submatrix e.symm e.symm) = relEnt A B := by
  rw [relEnt, relEnt, log_submatrix_equiv hA e, log_submatrix_equiv hB e]
  congr 2
  rw [show (CFC.log A).submatrix e.symm e.symm - (CFC.log B).submatrix e.symm e.symm
      = (CFC.log A - CFC.log B).submatrix e.symm e.symm from rfl]
  rw [Matrix.submatrix_mul_equiv]
  exact trace_submatrix_equiv _ e

/-! ### Conjugation by a unitary -/

lemma PosDef.conj_unitary {A : Matrix n n ℂ} (hA : A.PosDef) (u : unitary (Matrix n n ℂ)) :
    ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)).IsHermitian := by
    have hsA : star A = A := hA.1
    have : star ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ) := by
      simp only [StarMul.star_mul, star_star, mul_assoc, hsA]
    exact this
  refine ⟨hH, ?_⟩
  intro x hx
  have hxx : star (star (u : Matrix n n ℂ) *ᵥ x) ⬝ᵥ A *ᵥ (star (u : Matrix n n ℂ) *ᵥ x)
      = star x ⬝ᵥ ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ)) *ᵥ x := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul]
    simp [star_eq_conjTranspose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc]
  rw [← hxx]
  refine (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 ?_
  intro hc
  apply hx
  have : (u : Matrix n n ℂ) *ᵥ (star (u : Matrix n n ℂ) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, u.2.2, Matrix.one_mulVec]
  rw [hc] at this
  simpa using this.symm

lemma log_conj_unitary {A : Matrix n n ℂ} (hA : A.PosDef) (u : unitary (Matrix n n ℂ)) :
    CFC.log ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * CFC.log A * star (u : Matrix n n ℂ) :=
  (cfc_conj u hA.1 Real.log (continuousOn_log_spectrum hA)).symm

/-- The relative entropy is invariant under conjugation by a unitary. -/
theorem relEnt_conj_unitary {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (u : unitary (Matrix n n ℂ)) :
    relEnt ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
      ((u : Matrix n n ℂ) * B * star (u : Matrix n n ℂ)) = relEnt A B := by
  rw [relEnt, relEnt, log_conj_unitary hA u, log_conj_unitary hB u]
  set U : Matrix n n ℂ := (u : Matrix n n ℂ) with hU
  set L : Matrix n n ℂ := CFC.log A - CFC.log B with hL
  have h : star U * U = 1 := u.2.1
  have hsub : U * CFC.log A * star U - U * CFC.log B * star U = U * L * star U := by
    rw [hL]; simp [mul_sub, sub_mul]
  rw [hsub]
  have hprod : (U * A * star U) * (U * L * star U) = (U * (A * L)) * star U := by
    calc (U * A * star U) * (U * L * star U)
        = U * A * (star U * U) * L * star U := by simp only [mul_assoc]
      _ = U * (A * L) * star U := by rw [h]; simp [mul_assoc]
  rw [hprod, Matrix.trace_mul_comm, ← mul_assoc, h, one_mul]

/-! ### The embedding `Y ↦ 1 ⊗ Y` -/

lemma log_kronL {A : Matrix m m ℂ} (hA : A.PosDef) :
    CFC.log ((1 : Matrix n n ℂ) ⊗ₖ A) = (1 : Matrix n n ℂ) ⊗ₖ CFC.log A :=
  (cfc_kronL hA.1 Real.log (continuousOn_log_spectrum hA)).symm

/-! ### The embedding `X ↦ X ⊗ 1` -/

lemma log_kronR {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.log (A ⊗ₖ (1 : Matrix m m ℂ)) = CFC.log A ⊗ₖ (1 : Matrix m m ℂ) :=
  (cfc_kronR hA.1 Real.log (continuousOn_log_spectrum hA)).symm

/-- Tensoring with the identity multiplies the relative entropy by the dimension. -/
theorem relEnt_kronR {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    relEnt (A ⊗ₖ (1 : Matrix m m ℂ)) (B ⊗ₖ (1 : Matrix m m ℂ))
      = (Fintype.card m : ℝ) * relEnt A B := by
  rw [relEnt, relEnt, log_kronR (m := m) hA, log_kronR (m := m) hB]
  have hsub : CFC.log A ⊗ₖ (1 : Matrix m m ℂ) - CFC.log B ⊗ₖ (1 : Matrix m m ℂ)
      = (CFC.log A - CFC.log B) ⊗ₖ (1 : Matrix m m ℂ) := by
    ext p q
    simp [Matrix.kroneckerMap_apply, sub_mul]
  rw [hsub, ← Matrix.mul_kronecker_mul, one_mul, Matrix.trace_kronecker,
    Matrix.trace_one]
  simp [Complex.mul_re, mul_comm]

end QI

import RequestProject.SSA.Lift

/-!
# Joint convexity of the relative entropy

Letting `m → ∞` in the jointly concave functionals
`Qd m A B = Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))` gives the relative entropy, whence its joint
convexity (Lindblad).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix Filter Topology

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ}

/-- The scalar limit underlying the derivative formula for the relative entropy. -/
lemma dyseq_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun m : ℕ => 2 ^ m * (a - dyseq m a b)) atTop
      (𝓝 (a * (Real.log a - Real.log b))) := by
  set t : ℝ := Real.log b - Real.log a with ht
  have hexp : ∀ m : ℕ, dyseq m a b = a * Real.exp (t * ((2:ℝ)⁻¹ ^ m)) := by
    intro m
    set s : ℝ := (2:ℝ)⁻¹ ^ m with hs
    rw [dyseq_eq m ha hb, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    rw [← Real.exp_log ha, ← Real.exp_add]
    congr 1
    rw [Real.log_exp]
    ring
  have hbase : Tendsto (fun m : ℕ => (Real.exp (t * ((2:ℝ)⁻¹ ^ m)) - 1) / ((2:ℝ)⁻¹ ^ m))
      atTop (𝓝 t) := by
    have hd : HasDerivAt (fun s : ℝ => Real.exp (t * s)) t 0 := by
      have h1 : HasDerivAt (fun s : ℝ => t * s) t 0 := by
        simpa using (hasDerivAt_id (0:ℝ)).const_mul t
      simpa using h1.exp
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hs : Tendsto (fun m : ℕ => ((2:ℝ)⁻¹ ^ m)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), ?_⟩
      filter_upwards with m
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
    have h2 := hd.comp hs
    refine h2.congr fun m => ?_
    simp [slope_def_field]
  have hlim := hbase.const_mul (-a)
  have heq : ∀ m : ℕ, (-a) * ((Real.exp (t * ((2:ℝ)⁻¹ ^ m)) - 1) / ((2:ℝ)⁻¹ ^ m))
      = 2 ^ m * (a - dyseq m a b) := by
    intro m
    have hpow : ((2:ℝ)⁻¹ ^ m) = ((2:ℝ) ^ m)⁻¹ := by rw [inv_pow]
    have hne : ((2:ℝ) ^ m) ≠ 0 := by positivity
    rw [hexp m, hpow]
    field_simp
    ring
  have hval : (-a) * t = a * (Real.log a - Real.log b) := by rw [ht]; ring
  rw [← hval]
  exact hlim.congr heq

/-- The relative entropy is the limit of the (rescaled) dyadic trace functionals. -/
theorem relEnt_limit (hA : A.PosDef) (hB : B.PosDef) :
    Tendsto (fun m : ℕ => 2 ^ m * (A.trace.re - Qd m A B)) atTop (𝓝 (relEnt A B)) := by
  classical
  set lam := hA.1.eigenvalues
  set mu := hB.1.eigenvalues
  set c := ovl hA.1 hB.1
  have htr : A.trace.re = ∑ i, ∑ j, c i j * lam i := by
    have h1 : A.trace.re = ∑ i, lam i := by
      rw [hA.1.trace_eq_sum_eigenvalues]; simp; rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ovl_sum_right hA.1 hB.1 i, one_mul]
  have hrew : ∀ m : ℕ, 2 ^ m * (A.trace.re - Qd m A B)
      = ∑ i, ∑ j, c i j * (2 ^ m * (lam i - dyseq m (lam i) (mu j))) := by
    intro m
    rw [htr, Qd_eval hA hB m, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [relEnt_eq hA.1 hB.1]
  refine Tendsto.congr (fun m => (hrew m).symm) ?_
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  exact (dyseq_limit (hA.eigenvalues_pos i) (hB.eigenvalues_pos j)).const_mul (c i j)

lemma trace_re_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (A : ι → Matrix n n ℂ) :
    ((∑ i ∈ s, w i • A i).trace).re = ∑ i ∈ s, w i * ((A i).trace).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.trace_add, Complex.add_re, ih,
        Matrix.trace_smul]
      congr 1
      simp [Complex.real_smul, Complex.mul_re]

/-- **Joint convexity of the relative entropy**. -/
theorem relEnt_convex {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (R S : ι → Matrix n n ℂ) (hR : ∀ i ∈ s, (R i).PosDef) (hS : ∀ i ∈ s, (S i).PosDef)
    (hRsum : (∑ i ∈ s, w i • R i).PosDef) (hSsum : (∑ i ∈ s, w i • S i).PosDef) :
    relEnt (∑ i ∈ s, w i • R i) (∑ i ∈ s, w i • S i) ≤ ∑ i ∈ s, w i * relEnt (R i) (S i) := by
  have hstep : ∀ m : ℕ,
      2 ^ m * ((∑ i ∈ s, w i • R i).trace.re - Qd m (∑ i ∈ s, w i • R i) (∑ i ∈ s, w i • S i))
        ≤ ∑ i ∈ s, w i * (2 ^ m * ((R i).trace.re - Qd m (R i) (S i))) := by
    intro m
    have hcon := Qd_concave s w hw R S hR (fun i hi => (hS i hi).posSemidef) hRsum m
    rw [trace_re_sum]
    have : ∑ i ∈ s, w i * (2 ^ m * ((R i).trace.re - Qd m (R i) (S i)))
        = 2 ^ m * ((∑ i ∈ s, w i * (R i).trace.re) - ∑ i ∈ s, w i * Qd m (R i) (S i)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    have h2 : (0:ℝ) ≤ 2 ^ m := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  refine le_of_tendsto_of_tendsto' (relEnt_limit hRsum hSsum) ?_ hstep
  exact tendsto_finset_sum _ fun i hi => (relEnt_limit (hR i hi) (hS i hi)).const_mul (w i)

end QI

