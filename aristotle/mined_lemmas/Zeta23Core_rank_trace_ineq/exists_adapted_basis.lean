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
