import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/
def qform (Q : Matrix m m 𝕜) (x : m → 𝕜) : ℝ := RCLike.re (star x ⬝ᵥ Q *ᵥ x)

omit [DecidableEq m] in
@[simp] lemma qform_zero (Q : Matrix m m 𝕜) : qform Q 0 = 0 := by simp [qform]

open Classical in
/-- The positive index of inertia `n₊(Q)` of a Hermitian matrix: the number of positive
eigenvalues, counted with multiplicity.  (For non-Hermitian matrices it is set to `0`.) -/
noncomputable def posIndex (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then Fintype.card {i // 0 < h.eigenvalues i} else 0

lemma posIndex_eq_card {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    posIndex Q = Nat.card {i // 0 < hQ.eigenvalues i} := by
  classical
  simp [posIndex, hQ, Nat.card_eq_fintype_card]

/-- The `i`-th eigenvector of a Hermitian matrix, as a plain vector. -/
noncomputable def evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i : m) : m → 𝕜 :=
  ⇑(hQ.eigenvectorBasis i)

lemma evec_dotProduct {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i j : m) :
    star (evec hQ i) ⬝ᵥ evec hQ j = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.1 hQ.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [evec, dotProduct_comm] using h

lemma mulVec_evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i : m) :
    Q *ᵥ evec hQ i = hQ.eigenvalues i • evec hQ i :=
  hQ.mulVec_eigenvectorBasis i

lemma linearIndependent_evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    LinearIndependent 𝕜 (evec hQ) :=
  hQ.eigenvectorBasis.orthonormal.linearIndependent.map'
    (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap (by simp)

/-- The quadratic form evaluated on a linear combination of eigenvectors. -/
lemma qform_sum_evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (c : m → 𝕜) :
    qform Q (∑ i, c i • evec hQ i) = ∑ i, hQ.eigenvalues i * ‖c i‖ ^ 2 := by
  have h1 : Q *ᵥ (∑ i, c i • evec hQ i) = ∑ i, (c i * (hQ.eigenvalues i : 𝕜)) • evec hQ i := by
    rw [mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_smul, mulVec_evec, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
  rw [qform, h1, star_sum, sum_dotProduct]
  have key : ∀ i : m, (star (c i • evec hQ i)) ⬝ᵥ (∑ j, (c j * (hQ.eigenvalues j : 𝕜)) • evec hQ j)
      = (starRingEnd 𝕜) (c i) * (c i * (hQ.eigenvalues i : 𝕜)) := by
    intro i
    rw [dotProduct_sum, Finset.sum_eq_single i]
    · simp only [star_smul, smul_dotProduct, dotProduct_smul, evec_dotProduct, smul_eq_mul,
        if_pos, RCLike.star_def, mul_one]
      ring
    · intro j _ hj
      simp [star_smul, smul_dotProduct, dotProduct_smul, evec_dotProduct, smul_eq_mul,
        Ne.symm hj]
    · simp
  simp only [key]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (starRingEnd 𝕜) (c i) * (c i * (hQ.eigenvalues i : 𝕜))
      = ((‖c i‖ ^ 2 * hQ.eigenvalues i : ℝ) : 𝕜) := by
    rw [← mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  rw [h2, RCLike.ofReal_re]
  ring

/-- The span of the eigenvectors whose index satisfies `p`. -/
noncomputable def eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (p : m → Prop) :
    Submodule 𝕜 (m → 𝕜) :=
  Submodule.span 𝕜 (Set.range fun i : {i // p i} => evec hQ i)

lemma finrank_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (p : m → Prop) :
    finrank 𝕜 (eigenSpan hQ p) = Nat.card {i // p i} := by
  classical
  haveI : Fintype {i // p i} := Fintype.ofFinite _
  have hli : LinearIndependent 𝕜 (fun i : {i // p i} => evec hQ i) :=
    (linearIndependent_evec hQ).comp _ Subtype.val_injective
  rw [eigenSpan, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

lemma exists_coeff_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (p : m → Prop)
    {x : m → 𝕜} (hx : x ∈ eigenSpan hQ p) :
    ∃ c : m → 𝕜, (∀ i, ¬ p i → c i = 0) ∧ x = ∑ i, c i • evec hQ i := by
  classical
  haveI : Fintype {i // p i} := Fintype.ofFinite _
  obtain ⟨c₀, hc₀⟩ := (mem_span_range_iff_exists_fun 𝕜).1 hx
  refine ⟨fun i => if h : p i then c₀ ⟨i, h⟩ else 0, fun i hi => by simp [hi], ?_⟩
  rw [← hc₀]
  have hsub : ∑ i ∈ Finset.univ.filter p, (fun i => (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i) i
      = ∑ i : {i // p i}, (fun i => (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i) (i : m) :=
    Finset.sum_subtype _ (by simp) _
  have hzero : ∑ i : m, (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i
      = ∑ i ∈ Finset.univ.filter p, (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi]
  rw [hzero, hsub]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

lemma qform_nonpos_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {x : m → 𝕜}
    (hx : x ∈ eigenSpan hQ (fun i => hQ.eigenvalues i ≤ 0)) : qform Q x ≤ 0 := by
  obtain ⟨c, hc, rfl⟩ := exists_coeff_of_mem_eigenSpan hQ _ hx
  rw [qform_sum_evec]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : hQ.eigenvalues i ≤ 0
  · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
  · simp [hc i hi]

lemma qform_pos_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {x : m → 𝕜}
    (hx : x ∈ eigenSpan hQ (fun i => 0 < hQ.eigenvalues i)) (hx0 : x ≠ 0) : 0 < qform Q x := by
  obtain ⟨c, hc, rfl⟩ := exists_coeff_of_mem_eigenSpan hQ _ hx
  rw [qform_sum_evec]
  have hne : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (by simp [h])
  obtain ⟨i₀, hi₀⟩ := hne
  have hp : 0 < hQ.eigenvalues i₀ := by
    by_contra h
    exact hi₀ (hc i₀ h)
  refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
  · by_cases hi : 0 < hQ.eigenvalues i
    · positivity
    · simp [hc i hi]
  · have : 0 < ‖c i₀‖ ^ 2 := by positivity
    exact mul_pos hp this

lemma card_pos_add_card_nonpos {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    Nat.card {i // 0 < hQ.eigenvalues i} + Nat.card {i // hQ.eigenvalues i ≤ 0}
      = Fintype.card m := by
  classical
  haveI : Fintype {i // 0 < hQ.eigenvalues i} := Fintype.ofFinite _
  haveI : Fintype {i // ¬ (0 < hQ.eigenvalues i)} := Fintype.ofFinite _
  haveI : Fintype {i // hQ.eigenvalues i ≤ 0} := Fintype.ofFinite _
  have hcongr : Nat.card {i // hQ.eigenvalues i ≤ 0} = Nat.card {i // ¬ (0 < hQ.eigenvalues i)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i => by simp [not_lt])
  have hcompl : Fintype.card {i // ¬ (0 < hQ.eigenvalues i)}
      = Fintype.card m - Fintype.card {i // 0 < hQ.eigenvalues i} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i // 0 < hQ.eigenvalues i} ≤ Fintype.card m :=
    Fintype.card_subtype_le _
  rw [hcongr, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcompl]
  omega

/-- **Key lemma** (hard direction of Sylvester's law of inertia): the dimension of any subspace
on which `Q` is positive definite is at most the positive index of inertia of `Q`. -/
theorem finrank_le_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (m → 𝕜)) (hS : ∀ x ∈ S, x ≠ 0 → 0 < qform Q x) :
    finrank 𝕜 S ≤ posIndex Q := by
  classical
  set N : Submodule 𝕜 (m → 𝕜) := eigenSpan hQ (fun i => hQ.eigenvalues i ≤ 0)
  have hNrank : finrank 𝕜 N = Nat.card {i // hQ.eigenvalues i ≤ 0} := finrank_eigenSpan hQ _
  have hinf : S ⊓ N = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    by_contra hx0
    have h1 : 0 < qform Q x := hS x hx.1 hx0
    have h2 : qform Q x ≤ 0 := qform_nonpos_of_mem_eigenSpan hQ hx.2
    linarith
  have hsum : finrank 𝕜 (S ⊔ N : Submodule 𝕜 (m → 𝕜)) + finrank 𝕜 (S ⊓ N : Submodule 𝕜 (m → 𝕜))
      = finrank 𝕜 S + finrank 𝕜 N := Submodule.finrank_sup_add_finrank_inf_eq S N
  have hle : finrank 𝕜 (S ⊔ N : Submodule 𝕜 (m → 𝕜)) ≤ Fintype.card m := by
    have := Submodule.finrank_le (S ⊔ N : Submodule 𝕜 (m → 𝕜))
    rwa [Module.finrank_fintype_fun_eq_card] at this
  rw [hinf] at hsum
  simp only [finrank_bot, add_zero] at hsum
  have hcard := card_pos_add_card_nonpos hQ
  rw [posIndex_eq_card hQ]
  omega

/-- There is a subspace of dimension `posIndex Q` on which `Q` is positive definite. -/
theorem exists_posDef_subspace {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), finrank 𝕜 S = posIndex Q ∧ ∀ x ∈ S, x ≠ 0 → 0 < qform Q x := by
  refine ⟨eigenSpan hQ (fun i => 0 < hQ.eigenvalues i), ?_, fun x hx hx0 =>
    qform_pos_of_mem_eigenSpan hQ hx hx0⟩
  rw [finrank_eigenSpan, posIndex_eq_card hQ]

omit [DecidableEq m] in
lemma qform_conj (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜) (x : d → 𝕜) :
    qform Q (B *ᵥ x) = qform (Bᴴ * Q * B) x := by
  rw [qform, qform, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul,
    dotProduct_mulVec, vecMul_vecMul]
  simp [Matrix.mul_assoc, dotProduct_mulVec]

/-- **Inertia does not increase under compression**: for a Hermitian `Q` and any rectangular `B`,
the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le [DecidableEq d] {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  have hH : (Bᴴ * Q * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hQ
  refine ⟨hH, ?_⟩
  obtain ⟨S, hSdim, hSpos⟩ := exists_posDef_subspace hH
  set f : S →ₗ[𝕜] (m → 𝕜) := (Matrix.mulVecLin B).comp S.subtype
  have hfapply : ∀ y : S, f y = B *ᵥ (y : d → 𝕜) := fun y => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
    by_contra hy0
    have hyne : (y : d → 𝕜) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hpos : 0 < qform (Bᴴ * Q * B) (y : d → 𝕜) := hSpos _ y.2 hyne
    have hzero : B *ᵥ (y : d → 𝕜) = 0 := by
      have : f y = 0 := hy
      rwa [hfapply] at this
    rw [← qform_conj, hzero, qform_zero] at hpos
    exact lt_irrefl 0 hpos
  have hrange : ∀ x ∈ LinearMap.range f, x ≠ 0 → 0 < qform Q x := by
    rintro _ ⟨y, rfl⟩ hne
    rw [hfapply, qform_conj]
    refine hSpos _ y.2 fun h => hne ?_
    rw [hfapply, h, mulVec_zero]
  calc posIndex (Bᴴ * Q * B) = finrank 𝕜 S := hSdim.symm
    _ = finrank 𝕜 (LinearMap.range f) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ posIndex Q := finrank_le_posIndex hQ _ hrange

/-! ### Sanity checks -/

/-- The zero matrix has no positive eigenvalues. -/
lemma posIndex_zero : posIndex (0 : Matrix m m 𝕜) = 0 := by
  have hz : ∀ i, (isHermitian_zero (n := m) (α := 𝕜)).eigenvalues i = 0 := by
    have h := (Matrix.IsHermitian.eigenvalues_eq_zero_iff
      (isHermitian_zero (n := m) (α := 𝕜))).2 rfl
    exact fun i => congrFun h i
  rw [posIndex_eq_card (isHermitian_zero (n := m) (α := 𝕜))]
  have : IsEmpty {i : m // 0 < (isHermitian_zero (n := m) (α := 𝕜)).eigenvalues i} :=
    ⟨fun i => by simpa [hz i] using i.2⟩
  simp

/-- The identity matrix is positive definite: all `card m` of its eigenvalues are positive. -/
lemma posIndex_one : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  have h1 : ∀ i, (isHermitian_one (n := m) (α := 𝕜)).eigenvalues i = 1 := by
    intro i
    have h := (isHermitian_one (n := m) (α := 𝕜)).eigenvalues_eq i
    have h2 := (orthonormal_iff_ite.1
      (isHermitian_one (n := m) (α := 𝕜)).eigenvectorBasis.orthonormal) i i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
    simp only [if_pos] at h2
    rw [h, one_mulVec, dotProduct_comm, show
      (⇑((isHermitian_one (n := m) (α := 𝕜)).eigenvectorBasis i) ⬝ᵥ
        star ⇑((isHermitian_one (n := m) (α := 𝕜)).eigenvectorBasis i)) = 1 from h2]
    simp
  rw [posIndex_eq_card (isHermitian_one (n := m) (α := 𝕜))]
  have : ∀ i : m, 0 < (isHermitian_one (n := m) (α := 𝕜)).eigenvalues i := by
    intro i; rw [h1 i]; norm_num
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv this), Nat.card_eq_fintype_card]

end Zeta23Core

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

