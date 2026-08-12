import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/
lemma toEuclideanLin_apply' {n : Type*} [Fintype n] [DecidableEq n] {k : Type*}
    (M : Matrix k n 𝕜) (v : EuclideanSpace 𝕜 n) :
    Matrix.toEuclideanLin M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := rfl

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a matrix `Q`, viewed on
`EuclideanSpace 𝕜 m`. -/
noncomputable def qform (Q : Matrix m m 𝕜) (x : EuclideanSpace 𝕜 m) : ℝ :=
  RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin Q x))

/-- `Q` is positive definite on the subspace `S` if `xᴴ Q x > 0` for every nonzero `x ∈ S`. -/
def PosDefOn (Q : Matrix m m 𝕜) (S : Submodule 𝕜 (EuclideanSpace 𝕜 m)) : Prop :=
  ∀ x ∈ S, x ≠ 0 → 0 < qform Q x

/-- The positive index of inertia `n₊(Q)`: the number of positive eigenvalues of a Hermitian
matrix (and `0` for non-Hermitian matrices). -/
noncomputable def posIndex (Q : Matrix m m 𝕜) : ℕ :=
  if h : Q.IsHermitian then (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card else 0

lemma qform_eq_re_dotProduct (Q : Matrix m m 𝕜) (x : EuclideanSpace 𝕜 m) :
    qform Q x = RCLike.re (star x.ofLp ⬝ᵥ Q *ᵥ x.ofLp) := by
  rw [qform, EuclideanSpace.inner_eq_star_dotProduct, toEuclideanLin_apply']
  simp [dotProduct_comm]

/-- The quadratic form of the compression `Bᴴ Q B` is the quadratic form of `Q` evaluated at the
image vector `B x`. -/
lemma qform_conj (Q : Matrix m m 𝕜) (B : Matrix m d 𝕜) (x : EuclideanSpace 𝕜 d) :
    qform (Bᴴ * Q * B) x = qform Q (Matrix.toEuclideanLin B x) := by
  rw [qform_eq_re_dotProduct, qform_eq_re_dotProduct, toEuclideanLin_apply',
    WithLp.ofLp_toLp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

lemma toEuclideanLin_eigenvectorBasis {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i : m) :
    Matrix.toEuclideanLin Q (hQ.eigenvectorBasis i)
      = (hQ.eigenvalues i : 𝕜) • hQ.eigenvectorBasis i := by
  rw [toEuclideanLin_apply', hQ.mulVec_eigenvectorBasis, WithLp.toLp_smul, WithLp.toLp_ofLp,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)]

lemma inner_eigenvectorBasis_apply {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (i : m)
    (x : EuclideanSpace 𝕜 m) :
    inner 𝕜 (hQ.eigenvectorBasis i) (Matrix.toEuclideanLin Q x)
      = (hQ.eigenvalues i : 𝕜) * inner 𝕜 (hQ.eigenvectorBasis i) x := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hQ.eq]
  rw [← LinearMap.adjoint_inner_left, hadj, toEuclideanLin_eigenvectorBasis hQ i, inner_smul_left]
  simp

/-- Diagonalisation of the quadratic form in the eigenbasis. -/
lemma qform_eq_sum {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (x : EuclideanSpace 𝕜 m) :
    qform Q x = ∑ i, hQ.eigenvalues i * ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by
  rw [qform, ← (hQ.eigenvectorBasis).sum_inner_mul_inner x (Matrix.toEuclideanLin Q x), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_apply hQ i x, ← inner_conj_symm (𝕜 := 𝕜) (hQ.eigenvectorBasis i) x]
  set c : 𝕜 := inner 𝕜 x (hQ.eigenvectorBasis i) with hc
  rw [show c * ((hQ.eigenvalues i : 𝕜) * (starRingEnd 𝕜) c)
      = (hQ.eigenvalues i : 𝕜) * (c * (starRingEnd 𝕜) c) by ring, RCLike.mul_conj]
  simp

lemma eq_zero_of_inner_eigenvectorBasis_eq_zero {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (x : EuclideanSpace 𝕜 m) (h : ∀ i, inner 𝕜 (hQ.eigenvectorBasis i) x = 0) : x = 0 := by
  have hrepr : hQ.eigenvectorBasis.repr x = 0 := by
    ext i
    rw [OrthonormalBasis.repr_apply_apply]
    simp [h i]
  simpa using hQ.eigenvectorBasis.repr.injective (by simpa using hrepr)

/-- The span of the eigenvectors indexed by a finite set `T`. -/
noncomputable def eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (T : Finset m) :
    Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  Submodule.span 𝕜 (hQ.eigenvectorBasis '' (T : Set m))

lemma finrank_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (T : Finset m) :
    Module.finrank 𝕜 (eigenSpan hQ T) = T.card := by
  have hli : LinearIndependent 𝕜 (fun i : {i // i ∈ T} => hQ.eigenvectorBasis i) :=
    (hQ.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hrange : Set.range (fun i : {i // i ∈ T} => hQ.eigenvectorBasis i)
      = hQ.eigenvectorBasis '' (T : Set m) := by
    ext y
    simp [Set.mem_range, Set.mem_image]
  rw [eigenSpan, ← hrange, finrank_span_eq_card hli, Fintype.card_coe]

lemma inner_eq_zero_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (T : Finset m)
    {x : EuclideanSpace 𝕜 m} (hx : x ∈ eigenSpan hQ T) {i : m} (hi : i ∉ T) :
    inner 𝕜 (hQ.eigenvectorBasis i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := by rintro rfl; exact hi hj
      exact hQ.eigenvectorBasis.orthonormal.2 hij
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
  | smul a y _ hy => simp [inner_smul_right, hy]

/-- The set of indices of positive eigenvalues. -/
noncomputable def posSet {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) : Finset m :=
  Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)

lemma posIndex_eq_card {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    posIndex Q = (posSet hQ).card := by
  simp [posIndex, posSet, hQ]

/-- `Q` is positive definite on the span of the eigenvectors with positive eigenvalue. -/
lemma posDefOn_eigenSpan_posSet {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    PosDefOn Q (eigenSpan hQ (posSet hQ)) := by
  intro x hx hx0
  rw [qform_eq_sum hQ]
  refine Finset.sum_pos' (fun i _ => ?_) ?_
  · by_cases hi : i ∈ posSet hQ
    · have hpos : 0 < hQ.eigenvalues i := by simpa [posSet] using hi
      positivity
    · rw [inner_eq_zero_of_mem_eigenSpan hQ _ hx hi]
      simp
  · obtain ⟨i, hi⟩ : ∃ i, inner 𝕜 (hQ.eigenvectorBasis i) x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (eq_zero_of_inner_eigenvectorBasis_eq_zero hQ x h)
    have hiP : i ∈ posSet hQ := by
      by_contra hc
      exact hi (inner_eq_zero_of_mem_eigenSpan hQ _ hx hc)
    have hpos : 0 < hQ.eigenvalues i := by simpa [posSet] using hiP
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hnorm : 0 < ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by positivity
    positivity

/-- `Q` is nonpositive on the span of the eigenvectors with nonpositive eigenvalue. -/
lemma qform_nonpos_of_mem_eigenSpan_compl {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    {x : EuclideanSpace 𝕜 m} (hx : x ∈ eigenSpan hQ (posSet hQ)ᶜ) : qform Q x ≤ 0 := by
  rw [qform_eq_sum hQ]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ (posSet hQ)ᶜ
  · have hle : hQ.eigenvalues i ≤ 0 := by
      simp only [Finset.mem_compl, posSet, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hi
      exact hi
    have h2 : (0:ℝ) ≤ ‖inner 𝕜 (hQ.eigenvectorBasis i) x‖ ^ 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg hle h2
  · rw [inner_eq_zero_of_mem_eigenSpan hQ _ hx hi]
    simp

/-- Hard direction of Sylvester's law of inertia: any subspace on which `Q` is positive definite
has dimension at most `n₊(Q)`. -/
lemma finrank_le_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian)
    (S : Submodule 𝕜 (EuclideanSpace 𝕜 m)) (hS : PosDefOn Q S) :
    Module.finrank 𝕜 S ≤ posIndex Q := by
  set N := eigenSpan hQ (posSet hQ)ᶜ with hNdef
  have hinf : S ⊓ N = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have h1 := hS x hx.1 hx0
    have h2 := qform_nonpos_of_mem_eigenSpan_compl hQ hx.2
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S N
  rw [hinf] at hsum
  simp only [finrank_bot, add_zero] at hsum
  have hle : Module.finrank 𝕜 (S ⊔ N : Submodule 𝕜 (EuclideanSpace 𝕜 m)) ≤ Fintype.card m := by
    rw [← finrank_euclideanSpace (𝕜 := 𝕜) (ι := m)]
    exact Submodule.finrank_le _
  have hN : Module.finrank 𝕜 N = (posSet hQ)ᶜ.card := finrank_eigenSpan hQ _
  have hcard : (posSet hQ).card + (posSet hQ)ᶜ.card = Fintype.card m :=
    Finset.card_add_card_compl _
  rw [posIndex_eq_card hQ]
  omega

/-- Easy direction: there is a subspace of dimension `n₊(Q)` on which `Q` is positive definite. -/
lemma exists_posDefOn_finrank_eq_posIndex {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (EuclideanSpace 𝕜 m), Module.finrank 𝕜 S = posIndex Q ∧ PosDefOn Q S :=
  ⟨eigenSpan hQ (posSet hQ), by rw [finrank_eigenSpan, posIndex_eq_card],
    posDefOn_eigenSpan_posSet hQ⟩

/-- **Inertia does not increase under compression**: for a Hermitian matrix `Q` and any
rectangular matrix `B`, the compression `Bᴴ Q B` is Hermitian and `n₊(Bᴴ Q B) ≤ n₊(Q)`. -/
theorem posIndex_conj_le {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (B : Matrix m d 𝕜) :
    (Bᴴ * Q * B).IsHermitian ∧ posIndex (Bᴴ * Q * B) ≤ posIndex Q := by
  have hR : (Bᴴ * Q * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul B hQ
  refine ⟨hR, ?_⟩
  obtain ⟨S, hSdim, hSpos⟩ := exists_posDefOn_finrank_eq_posIndex hR
  set f := (Matrix.toEuclideanLin B).domRestrict S with hf
  have hzero : qform Q 0 = 0 := by simp [qform]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxS⟩ hker
    have hBx : Matrix.toEuclideanLin B x = 0 := by
      simpa [hf, LinearMap.domRestrict_apply] using hker
    by_contra hx0
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hlt := hSpos x hxS hx0'
    rw [qform_conj, hBx, hzero] at hlt
    exact lt_irrefl 0 hlt
  have hpos : PosDefOn Q (S.map (Matrix.toEuclideanLin B)) := by
    rintro y ⟨x, hxS, rfl⟩ hy0
    have hx0 : x ≠ 0 := by rintro rfl; simp at hy0
    rw [← qform_conj]
    exact hSpos x hxS hx0
  have hTdim : Module.finrank 𝕜 (S.map (Matrix.toEuclideanLin B)) = Module.finrank 𝕜 S := by
    rw [← LinearMap.range_domRestrict, ← hf]
    exact LinearMap.finrank_range_of_inj hinj
  calc posIndex (Bᴴ * Q * B)
      = Module.finrank 𝕜 (S.map (Matrix.toEuclideanLin B)) := by rw [hTdim, hSdim]
    _ ≤ posIndex Q := finrank_le_posIndex hQ _ hpos

/-- Sanity check that `posIndex` is not degenerate: the identity matrix has full positive index. -/
lemma posIndex_one : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  have hone : (1 : Matrix m m 𝕜).IsHermitian := Matrix.isHermitian_one
  have hqf : ∀ x : EuclideanSpace 𝕜 m, qform (1 : Matrix m m 𝕜) x = ‖x‖ ^ 2 := by
    intro x
    rw [qform, toEuclideanLin_apply', Matrix.one_mulVec, WithLp.toLp_ofLp,
      inner_self_eq_norm_sq_to_K]
    simp
  have hle : posIndex (1 : Matrix m m 𝕜) ≤ Fintype.card m := by
    rw [posIndex_eq_card hone, posSet]
    simpa using Finset.card_filter_le (Finset.univ : Finset m) _
  have hge : Fintype.card m ≤ posIndex (1 : Matrix m m 𝕜) := by
    have hpos : PosDefOn (1 : Matrix m m 𝕜) ⊤ := by
      intro x _ hx0
      rw [hqf x]
      have : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      positivity
    have := finrank_le_posIndex hone ⊤ hpos
    rwa [finrank_top, finrank_euclideanSpace] at this
  omega

end Zeta23Core

