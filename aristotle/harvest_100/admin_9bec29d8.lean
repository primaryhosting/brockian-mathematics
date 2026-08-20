/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/
noncomputable def frobSq (M : Matrix n n 𝕜) : ℝ := RCLike.re (Matrix.trace (Mᴴ * M))

/-- The positive index of a Hermitian matrix: the number of its positive eigenvalues. -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Fintype.card {i : n // 0 < hQ.eigenvalues i}

/-! ### Basis-independence of the diagonal sum -/

/-- The sum of the diagonal entries of an operator in an orthonormal basis does not depend on
the basis. -/
lemma sum_diag_eq {E ι κ : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (L : E →ₗ[𝕜] E)
    (f : OrthonormalBasis ι 𝕜 E) (g : OrthonormalBasis κ 𝕜 E) :
    ∑ i, inner 𝕜 (f i) (L (f i)) = ∑ j, inner 𝕜 (g j) (L (g j)) := by
  have h1 : ∀ i, inner 𝕜 (f i) (L (f i)) = ∑ j, inner 𝕜 (f i) (g j) * inner 𝕜 (g j) (L (f i)) :=
    fun i => (g.sum_inner_mul_inner (f i) (L (f i))).symm
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : ∀ i, inner 𝕜 (f i) (g j) * inner 𝕜 (g j) (L (f i))
      = inner 𝕜 ((LinearMap.adjoint L) (g j)) (f i) * inner 𝕜 (f i) (g j) := by
    intro i
    rw [LinearMap.adjoint_inner_left]
    ring
  simp_rw [h2]
  rw [f.sum_inner_mul_inner, LinearMap.adjoint_inner_left]

/-- The quadratic form of a matrix in terms of the inner product on `EuclideanSpace`. -/
lemma inner_toEuclideanLin (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    inner 𝕜 x (Matrix.toEuclideanLin M x) = star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x) := by
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, Pi.star_apply,
    RCLike.inner_apply, star_def]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma trace_eq_sum_diag {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    Matrix.trace M = ∑ i, inner 𝕜 (f i) (Matrix.toEuclideanLin M (f i)) := by
  rw [sum_diag_eq _ f (EuclideanSpace.basisFun n 𝕜)]
  simp [Matrix.trace, Matrix.diag, Matrix.toLpLin_apply, PiLp.inner_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

lemma frobSq_eq_sum_normSq {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    frobSq M = ∑ i, ‖Matrix.toEuclideanLin M (f i)‖ ^ 2 := by
  unfold frobSq
  rw [trace_eq_sum_diag _ f, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Matrix.toEuclideanLin (Mᴴ * M)
      = (LinearMap.adjoint (Matrix.toEuclideanLin M)) ∘ₗ (Matrix.toEuclideanLin M) := by
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [h]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K]
  simp

/-- In any orthonormal basis, the sum of the squares of the real parts of the diagonal entries
is at most the squared Frobenius norm. -/
lemma sum_sq_re_diag_le_frobSq {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    ∑ i, (RCLike.re (inner 𝕜 (f i) (Matrix.toEuclideanLin M (f i)))) ^ 2 ≤ frobSq M := by
  rw [frobSq_eq_sum_normSq M f]
  refine Finset.sum_le_sum fun i _ => ?_
  set L := Matrix.toEuclideanLin M
  have h1 : |RCLike.re (inner 𝕜 (f i) (L (f i)))| ≤ ‖(inner 𝕜 (f i) (L (f i)) : 𝕜)‖ :=
    RCLike.abs_re_le_norm _
  have h2 : ‖(inner 𝕜 (f i) (L (f i)) : 𝕜)‖ ≤ ‖f i‖ * ‖L (f i)‖ := norm_inner_le_norm _ _
  have h3 : ‖f i‖ = 1 := f.orthonormal.1 i
  rw [h3, one_mul] at h2
  nlinarith [h1.trans h2, sq_abs (RCLike.re (inner 𝕜 (f i) (L (f i)))),
    abs_nonneg (RCLike.re (inner 𝕜 (f i) (L (f i))))]

/-! ### The scalar core inequality -/

lemma scalar_core {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) (S U : Finset ι)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i ∉ S, q i ≤ 0) (hpz : ∀ i, i ∉ S → i ∉ U → p i = 0)
    {c : ℝ} (hc : 0 ≤ c) {r b : ℕ} (hS : S.card ≤ b) (hU : U.card ≤ r) :
    c * (∑ i, p i) - c ^ 2 / 4 * r + 2 * c * (∑ i, q i) - c ^ 2 * b
      ≤ ∑ i, (p i + q i) ^ 2 := by
  classical
  set w : ι → ℝ := fun i => (if i ∈ S then c ^ 2 else 0) + (if i ∈ U then c ^ 2 / 4 else 0)
    with hw
  have hwnn : ∀ i, 0 ≤ w i := by
    intro i
    simp only [hw]
    have h1 : (0:ℝ) ≤ if i ∈ S then c ^ 2 else 0 := by split <;> positivity
    have h2 : (0:ℝ) ≤ if i ∈ U then c ^ 2 / 4 else 0 := by split <;> positivity
    positivity
  have key : ∀ i, 2 * c * (p i + q i) - c * p i - w i ≤ (p i + q i) ^ 2 := by
    intro i
    by_cases hiS : i ∈ S
    · have h1 : (c ^ 2 : ℝ) ≤ w i := by
        simp only [hw, if_pos hiS]
        have : (0:ℝ) ≤ if i ∈ U then c ^ 2 / 4 else 0 := by split <;> positivity
        linarith
      nlinarith [sq_nonneg (p i + q i - c), hp i, mul_nonneg hc (hp i)]
    · have hqi : q i ≤ 0 := hq i hiS
      by_cases hiU : i ∈ U
      · have h1 : (c ^ 2 / 4 : ℝ) ≤ w i := by
          simp only [hw, if_neg hiS, if_pos hiU]; norm_num
        nlinarith [sq_nonneg (p i + q i - c / 2), mul_nonneg hc (neg_nonneg.mpr hqi)]
      · have hpi : p i = 0 := hpz i hiS hiU
        have h0 : 0 ≤ w i := hwnn i
        rw [hpi]
        nlinarith [sq_nonneg (q i), mul_nonneg hc (neg_nonneg.mpr hqi)]
  have hsum : ∑ i, w i ≤ c ^ 2 * b + c ^ 2 / 4 * r := by
    have e1 : ∑ i, (if i ∈ S then c ^ 2 else 0) = c ^ 2 * S.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
    have e2 : ∑ i, (if i ∈ U then c ^ 2 / 4 else 0) = c ^ 2 / 4 * U.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
    have e3 : ∑ i, w i = c ^ 2 * S.card + c ^ 2 / 4 * U.card := by
      simp only [hw, Finset.sum_add_distrib, e1, e2]
    rw [e3]
    have h1 : (S.card : ℝ) ≤ b := by exact_mod_cast hS
    have h2 : (U.card : ℝ) ≤ r := by exact_mod_cast hU
    have h3 : c ^ 2 * (S.card : ℝ) ≤ c ^ 2 * b := by nlinarith [sq_nonneg c]
    have h4 : c ^ 2 / 4 * (U.card : ℝ) ≤ c ^ 2 / 4 * r := by nlinarith [sq_nonneg c]
    linarith
  have step : ∑ i, (2 * c * (p i + q i) - c * p i - w i) ≤ ∑ i, (p i + q i) ^ 2 :=
    Finset.sum_le_sum fun i _ => key i
  have expand : ∑ i, (2 * c * (p i + q i) - c * p i - w i)
      = c * (∑ i, p i) + 2 * c * (∑ i, q i) - ∑ i, w i := by
    have h : ∀ i, 2 * c * (p i + q i) - c * p i - w i = c * p i + 2 * c * q i - w i := by
      intro i; ring
    simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [expand] at step
  linarith

/-! ### Existence of an adapted orthonormal basis -/

/-- The span of the eigenvectors of a Hermitian matrix belonging to its positive eigenvalues. -/
noncomputable def posSpan {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    Submodule 𝕜 (EuclideanSpace 𝕜 n) :=
  Submodule.span 𝕜 (Set.range (fun i : {i : n // 0 < hQ.eigenvalues i} =>
    (hQ.eigenvectorBasis i.1 : EuclideanSpace 𝕜 n)))

lemma finrank_posSpan_le {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    Module.finrank 𝕜 (posSpan hQ) ≤ posIndex hQ := by
  classical
  refine (finrank_span_le_card (R := 𝕜) _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)

/-- On the orthogonal complement of the span of its positive eigenvectors, a Hermitian matrix
has nonpositive quadratic form. -/
lemma re_inner_nonpos_of_mem_posSpan_orthogonal {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {x : EuclideanSpace 𝕜 n} (hx : x ∈ (posSpan hQ)ᗮ) :
    RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin Q x)) ≤ 0 := by
  set v := hQ.eigenvectorBasis with hv
  have hev : ∀ i, Matrix.toEuclideanLin Q (v i) = (hQ.eigenvalues i : 𝕜) • (v i) := by
    intro i
    apply WithLp.ofLp_injective (p := 2)
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, hv]
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hQ.mulVec_eigenvectorBasis i
  have hzero : ∀ i, 0 < hQ.eigenvalues i → inner 𝕜 (v i) x = 0 := by
    intro i hi
    refine (Submodule.mem_orthogonal _ _).1 hx (v i) ?_
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have key : inner 𝕜 x (Matrix.toEuclideanLin Q x)
      = ∑ i, ((hQ.eigenvalues i * ‖inner 𝕜 (v i) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← v.sum_inner_mul_inner x (Matrix.toEuclideanLin Q x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsym : (Matrix.toEuclideanLin Q).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hQ
    rw [← hsym (v i) x, hev i, inner_smul_left, RCLike.conj_ofReal, ← inner_conj_symm x (v i)]
    rw [show (starRingEnd 𝕜) (inner 𝕜 (v i) x) * ((hQ.eigenvalues i : 𝕜) * inner 𝕜 (v i) x)
        = (hQ.eigenvalues i : 𝕜) * (inner 𝕜 (v i) x * (starRingEnd 𝕜) (inner 𝕜 (v i) x)) from by
      ring, RCLike.mul_conj]
    push_cast
    ring
  rw [key, map_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [RCLike.ofReal_re]
  rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
  · rw [hzero i h]; simp
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- A subfamily of an orthonormal basis contained in a subspace has at most `finrank` many
members. -/
lemma card_le_finrank_of_mem {E ι : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (g : OrthonormalBasis ι 𝕜 E) (T : Finset ι)
    (V : Submodule 𝕜 E) (h : ∀ k ∈ T, g k ∈ V) : T.card ≤ Module.finrank 𝕜 V := by
  classical
  have hli : LinearIndependent 𝕜 (fun k : T => (⟨g k, h k k.2⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hc : (V.subtype ∘ fun k : T => (⟨g k, h k k.2⟩ : V)) = fun k : T => g (k : ι) := rfl
    rw [hc]
    exact (g.orthonormal.comp (fun k : T => (k : ι)) Subtype.val_injective).linearIndependent
  simpa using LinearIndependent.fintype_card_le_finrank hli

lemma exists_adapted_basis {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    ∃ (d : ℕ) (f : OrthonormalBasis (Fin d) 𝕜 (EuclideanSpace 𝕜 n)) (S U : Finset (Fin d)),
      S.card ≤ b ∧ U.card ≤ r ∧
      (∀ k ∉ S, RCLike.re (inner 𝕜 (f k) (Matrix.toEuclideanLin Q (f k))) ≤ 0) ∧
      (∀ k, k ∉ S → k ∉ U → RCLike.re (inner 𝕜 (f k) (Matrix.toEuclideanLin P (f k))) = 0) := by
  classical
  set W := posSpan hQ with hWdef
  set Pw : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := (W.starProjection).toLinearMap
    with hPwdef
  set Pt : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := (Wᗮ.starProjection).toLinearMap
    with hPtdef
  set Pop := Matrix.toEuclideanLin P with hPopdef
  set A : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := Pt ∘ₗ Pop ∘ₗ Pt with hAdef
  set B : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n := A - Pw with hBdef
  -- elementary properties of the two orthogonal projections
  have hPopsym : Pop.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hP.1
  have hPwsym : ∀ u v, inner 𝕜 (Pw u) v = inner 𝕜 u (Pw v) :=
    fun u v => Submodule.inner_starProjection_left_eq_right W u v
  have hPtsym : ∀ u v, inner 𝕜 (Pt u) v = inner 𝕜 u (Pt v) :=
    fun u v => Submodule.inner_starProjection_left_eq_right Wᗮ u v
  have hAapp : ∀ u, A u = Pt (Pop (Pt u)) := fun u => rfl
  have hBapp : ∀ u, B u = A u - Pw u := fun u => rfl
  have hPwmem : ∀ u, Pw u ∈ W := fun u => W.starProjection_apply_mem u
  have hPtmem : ∀ u, Pt u ∈ Wᗮ := fun u => Wᗮ.starProjection_apply_mem u
  have hPtfix : ∀ u, u ∈ Wᗮ → Pt u = u := fun _ hu => Submodule.starProjection_eq_self_iff.2 hu
  have hPwzero : ∀ u, u ∈ Wᗮ → Pw u = 0 :=
    fun _ hu => (Submodule.starProjection_apply_eq_zero_iff W).2 hu
  have hPtidem : ∀ u, Pt (Pt u) = Pt u := fun u => hPtfix _ (hPtmem u)
  have hPwidem : ∀ u, Pw (Pw u) = Pw u :=
    fun u => Submodule.starProjection_eq_self_iff.2 (hPwmem u)
  have hPwPt : ∀ u, Pw (Pt u) = 0 := fun u => hPwzero _ (hPtmem u)
  have hPtPw : ∀ u, Pt (Pw u) = 0 := fun u =>
    (Submodule.starProjection_apply_eq_zero_iff Wᗮ).2
      (Submodule.le_orthogonal_orthogonal W (hPwmem u))
  have hsplit : ∀ u, Pw u + Pt u = u := by
    intro u
    have h : Wᗮ.starProjection = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 n) - W.starProjection :=
      Submodule.starProjection_orthogonal W
    simp [hPtdef, hPwdef, h]
  have hPtA : ∀ u, Pt (A u) = A u := by
    intro u; rw [hAapp u, hPtidem]
  -- `B` is symmetric, so it has an orthonormal eigenbasis
  have hBsym : B.IsSymmetric := by
    intro x y
    rw [hBapp, hBapp, inner_sub_left, inner_sub_right, hAapp, hAapp, hPtsym, hPopsym,
      ← hPtsym, hPwsym]
  set d := Module.finrank 𝕜 (EuclideanSpace 𝕜 n) with hddef
  set f := hBsym.eigenvectorBasis (rfl : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) = d) with hfdef
  set β := hBsym.eigenvalues (rfl : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) = d) with hbetadef
  have heig : ∀ k, B (f k) = ((β k : 𝕜)) • f k := fun k =>
    hBsym.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) = d) k
  have hPnonneg : ∀ u, 0 ≤ RCLike.re (inner 𝕜 u (Pop u)) := by
    intro u
    rw [hPopdef, inner_toEuclideanLin]
    exact hP.re_dotProduct_nonneg _
  -- eigenvectors with nonnegative eigenvalue are orthogonal to `W`
  have hPwf : ∀ k, 0 ≤ β k → Pw (f k) = 0 := by
    intro k hk
    have h1 : Pw (B (f k)) = - Pw (f k) := by
      rw [hBapp, map_sub, hAapp, hPwPt, hPwidem, zero_sub]
    have h2 : Pw (B (f k)) = (β k : 𝕜) • Pw (f k) := by rw [heig k, map_smul]
    have h3 : ((β k : 𝕜) + 1) • Pw (f k) = 0 := by
      rw [add_smul, one_smul, ← h2, h1, neg_add_cancel]
    have h4 : ((β k : 𝕜) + 1) ≠ 0 := by
      have h5 : ((β k + 1 : ℝ) : 𝕜) ≠ 0 := by
        rw [ne_eq, RCLike.ofReal_eq_zero]
        linarith
      push_cast at h5
      exact h5
    exact (smul_eq_zero.1 h3).resolve_left h4
  have hfperp : ∀ k, 0 ≤ β k → f k ∈ Wᗮ := fun k hk =>
    (Submodule.starProjection_apply_eq_zero_iff W).1 (hPwf k hk)
  have hAf : ∀ k, A (f k) = (β k : 𝕜) • Pt (f k) := by
    intro k
    have h1 : Pt (B (f k)) = A (f k) := by rw [hBapp, map_sub, hPtPw, sub_zero, hPtA]
    have h2 : Pt (B (f k)) = (β k : 𝕜) • Pt (f k) := by rw [heig k, map_smul]
    rw [← h1, h2]
  have hquadA : ∀ k, inner 𝕜 (f k) (A (f k)) = inner 𝕜 (Pt (f k)) (Pop (Pt (f k))) := by
    intro k; rw [hAapp, ← hPtsym]
  have hquadA2 : ∀ k, inner 𝕜 (f k) (A (f k)) = (β k : 𝕜) * ((‖Pt (f k)‖ ^ 2 : ℝ) : 𝕜) := by
    intro k
    have hin : inner 𝕜 (f k) (Pt (f k)) = ((‖Pt (f k)‖ ^ 2 : ℝ) : 𝕜) := by
      have h : inner 𝕜 (f k) (Pt (f k)) = inner 𝕜 (Pt (f k)) (Pt (f k)) := by
        conv_lhs => rw [← hPtidem (f k)]
        rw [← hPtsym]
      rw [h, inner_self_eq_norm_sq_to_K]
      push_cast
      ring
    rw [hAf k, inner_smul_right, hin]
  -- eigenvectors with negative eigenvalue lie in `W`
  have hPtzero : ∀ k, β k < 0 → Pt (f k) = 0 := by
    intro k hk
    have h3 : 0 ≤ RCLike.re (inner 𝕜 (f k) (A (f k))) := by
      rw [hquadA k]; exact hPnonneg _
    rw [hquadA2 k] at h3
    have h4 : RCLike.re ((β k : 𝕜) * ((‖Pt (f k)‖ ^ 2 : ℝ) : 𝕜)) = β k * ‖Pt (f k)‖ ^ 2 := by
      rw [← RCLike.ofReal_mul, RCLike.ofReal_re]
    rw [h4] at h3
    have h6 : ‖Pt (f k)‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖Pt (f k)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [pow_pos hpos 2]
    exact norm_eq_zero.1 h6
  have hfW : ∀ k, β k < 0 → f k ∈ W := by
    intro k hk
    have h := hsplit (f k)
    rw [hPtzero k hk, add_zero] at h
    rw [← h]
    exact hPwmem _
  -- eigenvectors with positive eigenvalue lie in the range of `A`
  have hfrange : ∀ k, 0 < β k → f k ∈ LinearMap.range A := by
    intro k hk
    have hne : (β k : 𝕜) ≠ 0 := by
      rw [ne_eq, RCLike.ofReal_eq_zero]
      linarith
    refine ⟨((β k : 𝕜)⁻¹) • f k, ?_⟩
    rw [map_smul, hAf k, hPtfix _ (hfperp k hk.le), smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hrankA : Module.finrank 𝕜 (LinearMap.range A) ≤ P.rank := by
    have h1 : LinearMap.range A = Submodule.map Pt (LinearMap.range (Pop ∘ₗ Pt)) :=
      LinearMap.range_comp _ _
    rw [h1]
    refine (Submodule.finrank_map_le _ _).trans ?_
    refine (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans ?_
    exact le_of_eq (Matrix.rank_eq_finrank_range_toLin P (EuclideanSpace.basisFun n 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis).symm
  refine ⟨d, f, Finset.univ.filter (fun k => β k < 0), Finset.univ.filter (fun k => 0 < β k),
    ?_, ?_, ?_, ?_⟩
  · refine (card_le_finrank_of_mem f _ W fun k hk => hfW k ?_).trans
      ((finrank_posSpan_le hQ).trans hb)
    simpa using hk
  · refine (card_le_finrank_of_mem f _ (LinearMap.range A) fun k hk => hfrange k ?_).trans
      (hrankA.trans hr)
    simpa using hk
  · intro k hk
    have hk' : 0 ≤ β k := by
      have : ¬ (β k < 0) := by simpa using hk
      linarith [not_lt.1 this]
    exact re_inner_nonpos_of_mem_posSpan_orthogonal hQ (hfperp k hk')
  · intro k hk1 hk2
    have h1 : 0 ≤ β k := by
      have : ¬ (β k < 0) := by simpa using hk1
      linarith [not_lt.1 this]
    have h2 : ¬ (0 < β k) := by simpa using hk2
    have h3 : β k = 0 := le_antisymm (not_lt.1 h2) h1
    have h5 : Pt (f k) = f k := hPtfix _ (hfperp k h1)
    have h6 : inner 𝕜 (f k) (Pop (f k)) = 0 := by
      have h7 := hquadA k
      rw [h5] at h7
      rw [← h7, hquadA2 k, h3]
      simp
    rw [h6]
    simp

/-! ### The rank–trace inequality -/

/-- **Rank–trace inequality.**  Let `P` be a positive semidefinite matrix of rank at most `r`,
let `Q` be a Hermitian matrix with at most `b` positive eigenvalues, and let `c > 0`.  Then
`c·Re tr P − (c²/4)·r + 2c·Re tr Q − c²·b ≤ ‖P + Q‖_F²`.
(The proof only uses `0 ≤ c`.) -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * RCLike.re (Matrix.trace P) - c ^ 2 / 4 * r + 2 * c * RCLike.re (Matrix.trace Q)
      - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  obtain ⟨d, f, S, U, hScard, hUcard, hQneg, hPzero⟩ := exists_adapted_basis hP hQ hr hb
  set p : Fin d → ℝ := fun k => RCLike.re (inner 𝕜 (f k) (Matrix.toEuclideanLin P (f k)))
    with hpdef
  set q : Fin d → ℝ := fun k => RCLike.re (inner 𝕜 (f k) (Matrix.toEuclideanLin Q (f k)))
    with hqdef
  have hpsum : ∑ k, p k = RCLike.re (Matrix.trace P) := by
    rw [trace_eq_sum_diag P f, map_sum]
  have hqsum : ∑ k, q k = RCLike.re (Matrix.trace Q) := by
    rw [trace_eq_sum_diag Q f, map_sum]
  have hsum : ∀ k, p k + q k
      = RCLike.re (inner 𝕜 (f k) (Matrix.toEuclideanLin (P + Q) (f k))) := by
    intro k
    rw [map_add, LinearMap.add_apply, inner_add_right, map_add]
  have hpnn : ∀ k, 0 ≤ p k := by
    intro k
    rw [hpdef]
    simp only [inner_toEuclideanLin]
    exact hP.re_dotProduct_nonneg _
  have hfrob : ∑ k, (p k + q k) ^ 2 ≤ frobSq (P + Q) := by
    simp_rw [hsum]
    exact sum_sq_re_diag_le_frobSq (P + Q) f
  have := scalar_core p q S U hpnn hQneg hPzero hc.le hScard hUcard
  rw [hpsum, hqsum] at this
  linarith

end Zeta23Core

