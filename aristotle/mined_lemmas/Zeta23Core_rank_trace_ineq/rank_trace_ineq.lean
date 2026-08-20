import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem rank_trace_ineq [DecidableEq n] {P Q : Matrix n n 𝕜} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (r b : ℕ) (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) (c : ℝ) (hc : 0 < c) :
    c * RCLike.re (Matrix.trace P) - c ^ 2 / 4 * r + 2 * c * RCLike.re (Matrix.trace Q)
      - c ^ 2 * b ≤ fro2 (P + Q) := by
  classical
  -- spectral data of `Q`
  set U : Matrix n n 𝕜 := (hQ.eigenvectorUnitary : Matrix n n 𝕜) with hUdef
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hQ.eigenvectorUnitary.2
  set lam : n → ℝ := hQ.eigenvalues with hlamdef
  have hQspec : Q = U * diagonal (RCLike.ofReal ∘ lam) * Uᴴ := hQ.spectral_theorem
  set dV : n → 𝕜 := fun i => if 0 < lam i then 1 else 0 with hdVdef
  set PV : Matrix n n 𝕜 := U * diagonal dV * Uᴴ with hPVdef
  have hPVh : PVᴴ = PV := by
    refine udu_conjTranspose U fun i => ?_
    by_cases h : 0 < lam i <;> simp [hdVdef, h]
  have hPVi : PV * PV = PV := by
    have hdd : (fun i => dV i * dV i) = dV := by
      funext i; by_cases h : 0 < lam i <;> simp [hdVdef, h]
    rw [hPVdef, udu_mul_udu hU1, hdd]
  -- the auxiliary matrices for the second projection
  set M : Matrix n n 𝕜 := (1 - PV) * P with hMdef
  set G : Matrix n n 𝕜 := M * Mᴴ with hGdef
  have hGh : G.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  set U2 : Matrix n n 𝕜 := (hGh.eigenvectorUnitary : Matrix n n 𝕜) with hU2def
  have hU21 : U2ᴴ * U2 = 1 := Matrix.mem_unitaryGroup_iff'.mp hGh.eigenvectorUnitary.2
  set mu : n → ℝ := hGh.eigenvalues with hmudef
  have hGspec : G = U2 * diagonal (RCLike.ofReal ∘ mu) * U2ᴴ := hGh.spectral_theorem
  set dW : n → 𝕜 := fun i => if mu i ≠ 0 then 1 else 0 with hdWdef
  set PW : Matrix n n 𝕜 := U2 * diagonal dW * U2ᴴ with hPWdef
  have hPWh : PWᴴ = PW := by
    refine udu_conjTranspose U2 fun i => ?_
    by_cases h : mu i ≠ 0 <;> simp [hdWdef, h]
  have hPWi : PW * PW = PW := by
    have hdd : (fun i => dW i * dW i) = dW := by
      funext i; by_cases h : mu i = 0 <;> simp [hdWdef, h]
    rw [hPWdef, udu_mul_udu hU21, hdd]
  -- traces of the projections
  have htrPV : RCLike.re (Matrix.trace PV) = (posIndex hQ : ℝ) := by
    rw [hPVdef, hdVdef, trace_indicator_proj hU1 (fun i => 0 < lam i)]
    simp [posIndex, hlamdef]
  have hcardW : RCLike.re (Matrix.trace PW) = (Fintype.card {i // mu i ≠ 0} : ℝ) := by
    rw [hPWdef, hdWdef]
    exact trace_indicator_proj hU21 (fun i => mu i ≠ 0)
  have htrPW : RCLike.re (Matrix.trace PW) ≤ (r : ℝ) := by
    have hrankG : G.rank = Fintype.card {i // mu i ≠ 0} := hGh.rank_eq_card_non_zero_eigs
    have hGle : G.rank ≤ r := by
      rw [hGdef, Matrix.rank_self_mul_conjTranspose, hMdef]
      exact le_trans (Matrix.rank_mul_le_right _ _) hr
    rw [hcardW, ← hrankG]
    exact_mod_cast hGle
  have htrPWnn : (0:ℝ) ≤ RCLike.re (Matrix.trace PW) := by
    rw [hcardW]; positivity
  -- the key trace inequalities
  have hQtrace : RCLike.re (Matrix.trace Q) = ∑ i, lam i := by
    rw [hQ.trace_eq_sum_eigenvalues, map_sum]
    simp [hlamdef]
  have htrPVQ : RCLike.re (Matrix.trace Q) ≤ RCLike.re (Matrix.trace (PV * Q)) := by
    have hval : RCLike.re (Matrix.trace (PV * Q)) = ∑ i, (if 0 < lam i then lam i else 0) := by
      conv_lhs => rw [hQspec, hPVdef, hdVdef]
      exact trace_indicator_proj_mul hU1 (fun i => 0 < lam i) lam
    rw [hval, hQtrace]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : 0 < lam i
    · simp [h]
    · simp only [h, if_false]
      exact not_lt.mp h
  have htrPVP : 0 ≤ RCLike.re (Matrix.trace (PV * P)) := by
    rw [re_trace_proj_mul_eq PV P hPVh hPVi]
    exact Finset.sum_nonneg fun a _ => hP.re_dotProduct_nonneg _
  -- `Q` is nonpositive on the orthogonal complement of the positive spectral subspace
  have hQneg : ∀ y : n → 𝕜, PV *ᵥ y = 0 → RCLike.re (star y ⬝ᵥ (Q *ᵥ y)) ≤ 0 := by
    intro y hy
    rw [hQspec]
    refine quad_indicator_proj_nonpos hU1 (fun i => 0 < lam i) lam (fun i hi => not_lt.mp hi) y ?_
    rw [← hdVdef, ← hPVdef]
    exact hy
  -- the two projections are orthogonal
  have hPVG : PV * G = 0 := by
    have h0 : PV * M = 0 := by
      rw [hMdef, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPVi, sub_self,
        Matrix.zero_mul]
    rw [hGdef, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  have hPVPW : PV * PW = 0 := by
    rw [hPWdef, hdWdef]
    refine indicator_proj_annihilates mu hU21 ?_
    rw [← hGspec]
    exact hPVG
  have hPWPV : PW * PV = 0 := by
    have := congrArg Matrix.conjTranspose hPVPW
    rwa [Matrix.conjTranspose_mul, hPVh, hPWh, Matrix.conjTranspose_zero] at this
  -- `PW` is the identity on the range of `M`
  have hPWG : PW * G = G := by
    have hdd : (fun i => dW i * (RCLike.ofReal ∘ mu) i) = (RCLike.ofReal ∘ mu) := by
      funext i
      by_cases h : mu i = 0 <;> simp [hdWdef, h, Function.comp]
    conv_lhs => rw [hPWdef, hGspec]
    rw [udu_mul_udu hU21, hdd, ← hGspec]
  have hPWM : PW * M = M := proj_mul_eq_self hPWh (by rw [← hGdef]; exact hPWG)
  -- `P` vanishes on the orthogonal complement of the two projections
  have hPzero : ∀ y : n → 𝕜, PV *ᵥ y = 0 → PW *ᵥ y = 0 → star y ⬝ᵥ (P *ᵥ y) = 0 := by
    intro y hyV hyW
    have h1 : star y ⬝ᵥ (M *ᵥ y) = star y ⬝ᵥ (P *ᵥ y) := by
      rw [hMdef, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dot_of_herm_mulVec_zero hPVh (P *ᵥ y) hyV, sub_zero]
    have h2 : star y ⬝ᵥ (M *ᵥ y) = 0 := by
      conv_lhs => rw [← hPWM]
      rw [← Matrix.mulVec_mulVec]
      exact dot_of_herm_mulVec_zero hPWh (M *ᵥ y) hyW
    rw [← h1, h2]
  -- the residual projection
  set PR : Matrix n n 𝕜 := 1 - PV - PW with hPRdef
  have hPRh : PRᴴ = PR := by
    rw [hPRdef]
    simp [Matrix.conjTranspose_sub, hPVh, hPWh]
  have hPVPR : PV * PR = 0 := by
    rw [hPRdef, Matrix.mul_sub, Matrix.mul_sub, hPVi, hPVPW, Matrix.mul_one]
    simp
  have hPWPR : PW * PR = 0 := by
    rw [hPRdef, Matrix.mul_sub, Matrix.mul_sub, hPWi, hPWPV, Matrix.mul_one]
    simp
  have hPRi : PR * PR = PR := by
    have h1 : PR * PV = 0 := by
      rw [hPRdef, Matrix.sub_mul, Matrix.sub_mul, hPVi, hPWPV, Matrix.one_mul]
      simp
    have h2 : PR * PW = 0 := by
      rw [hPRdef, Matrix.sub_mul, Matrix.sub_mul, hPWi, hPVPW, Matrix.one_mul]
      simp
    conv_lhs => rw [hPRdef]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, h1, h2]
    simp [hPRdef]
  -- the trace splitting
  have htrsplit : RCLike.re (Matrix.trace (P + Q))
      ≤ RCLike.re (Matrix.trace (PV * (P + Q))) + RCLike.re (Matrix.trace (PW * (P + Q))) := by
    have hsum1 : PV + PW + PR = 1 := by rw [hPRdef]; abel
    have htrPR : RCLike.re (Matrix.trace (PR * (P + Q))) ≤ 0 := by
      rw [re_trace_proj_mul_eq PR (P + Q) hPRh hPRi]
      refine Finset.sum_nonpos fun a _ => ?_
      have hyV : PV *ᵥ (fun b => PR b a) = 0 := mulVec_col_eq_zero hPVPR a
      have hyW : PW *ᵥ (fun b => PR b a) = 0 := mulVec_col_eq_zero hPWPR a
      have hsplit : star (fun b => PR b a) ⬝ᵥ ((P + Q) *ᵥ (fun b => PR b a))
          = star (fun b => PR b a) ⬝ᵥ (P *ᵥ (fun b => PR b a))
            + star (fun b => PR b a) ⬝ᵥ (Q *ᵥ (fun b => PR b a)) := by
        rw [Matrix.add_mulVec, dotProduct_add]
      rw [hsplit, map_add, hPzero _ hyV hyW]
      simpa using hQneg _ hyV
    have hdecomp : Matrix.trace (P + Q) = Matrix.trace (PV * (P + Q))
        + Matrix.trace (PW * (P + Q)) + Matrix.trace (PR * (P + Q)) := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, hsum1,
        Matrix.one_mul]
    rw [hdecomp, map_add, map_add]
    linarith
  -- the test matrix
  set X : Matrix n n 𝕜 := (c : 𝕜) • PV + ((c / 2 : ℝ) : 𝕜) • PW with hXdef
  have hXh : X.IsHermitian := by
    show Xᴴ = X
    rw [hXdef, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      hPVh, hPWh]
    simp [RCLike.star_def]
  have hAh : (P + Q).IsHermitian := hP.1.add hQ
  have hXX : X * X = ((c ^ 2 : ℝ) : 𝕜) • PV + ((c ^ 2 / 4 : ℝ) : 𝕜) • PW := by
    rw [hXdef]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hPVi, hPWi,
      hPVPW, hPWPV, smul_zero, add_zero, zero_add]
    rw [smul_smul, smul_smul]
    congr 2 <;> · push_cast; ring
  have hfro2X : fro2 X = c ^ 2 * RCLike.re (Matrix.trace PV)
      + c ^ 2 / 4 * RCLike.re (Matrix.trace PW) := by
    unfold fro2
    rw [hXh.eq, hXX, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, map_add,
      smul_eq_mul, smul_eq_mul, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
  have htrXA : RCLike.re (Matrix.trace (X * (P + Q)))
      = c * RCLike.re (Matrix.trace (PV * (P + Q)))
        + c / 2 * RCLike.re (Matrix.trace (PW * (P + Q))) := by
    rw [hXdef, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul, map_add, smul_eq_mul, smul_eq_mul,
      RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
  have hmain := fro2_ge (P + Q) X hAh hXh
  rw [htrXA, hfro2X] at hmain
  -- assemble
  have htPV : RCLike.re (Matrix.trace (PV * (P + Q)))
      = RCLike.re (Matrix.trace (PV * P)) + RCLike.re (Matrix.trace (PV * Q)) := by
    rw [Matrix.mul_add, Matrix.trace_add, map_add]
  have htPQ : RCLike.re (Matrix.trace (P + Q))
      = RCLike.re (Matrix.trace P) + RCLike.re (Matrix.trace Q) := by
    rw [Matrix.trace_add, map_add]
  have hdv : RCLike.re (Matrix.trace PV) ≤ (b : ℝ) := by
    rw [htrPV]; exact_mod_cast hb
  have hc2 : (0:ℝ) ≤ c ^ 2 := sq_nonneg c
  nlinarith [hmain, htrPVQ, htrPVP, htrsplit, htrPW, hdv, hc.le, htrPWnn]

end Zeta23Core

