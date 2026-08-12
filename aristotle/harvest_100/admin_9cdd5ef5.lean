/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Redux
namespace LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a complex matrix. -/
noncomputable def rtrace (X : Matrix n n ℂ) : ℝ := (X.trace).re

/-- The squared Frobenius norm `Re (tr (Xᴴ * X))` of a complex matrix. -/
noncomputable def frobSq (X : Matrix n n ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity).  For non-Hermitian matrices this is `0`. -/
noncomputable def posIndex (Q : Matrix n n ℂ) : ℕ :=
  if h : Q.IsHermitian then
    (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card
  else 0

/-- Conjugation of a real diagonal matrix by a unitary. -/
noncomputable def conjD (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (f i : ℂ)) * (star U : Matrix n n ℂ)

/-! ### Basic properties of `rtrace` and `frobSq` -/

omit [DecidableEq n] in
lemma rtrace_add (X Y : Matrix n n ℂ) : rtrace (X + Y) = rtrace X + rtrace Y := by
  simp [rtrace, Matrix.trace_add]

omit [DecidableEq n] in
lemma rtrace_sub (X Y : Matrix n n ℂ) : rtrace (X - Y) = rtrace X - rtrace Y := by
  simp [rtrace, Matrix.trace_sub]

omit [DecidableEq n] in
lemma rtrace_zero : rtrace (0 : Matrix n n ℂ) = 0 := by simp [rtrace]

omit [DecidableEq n] in
lemma rtrace_mul_comm (X Y : Matrix n n ℂ) : rtrace (X * Y) = rtrace (Y * X) := by
  rw [rtrace, rtrace, Matrix.trace_mul_comm]

lemma rtrace_smul_one_mul (k : ℝ) (X : Matrix n n ℂ) :
    rtrace (X * ((k : ℂ) • (1 : Matrix n n ℂ))) = k * rtrace X := by
  rw [Matrix.mul_smul, Matrix.mul_one, rtrace, rtrace, Matrix.trace_smul]
  simp

omit [DecidableEq n] in
lemma frobSq_nonneg (X : Matrix n n ℂ) : 0 ≤ frobSq X := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  simpa [frobSq] using (Complex.le_def.mp h).1

omit [DecidableEq n] in
lemma frobSq_of_isHermitian {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    frobSq X = rtrace (X * X) := by
  rw [frobSq, rtrace, hX.eq]

omit [DecidableEq n] in
lemma frobSq_add_of_isHermitian {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + 2 * rtrace (X * Y) + frobSq Y := by
  have h1 : (X + Y)ᴴ * (X + Y) = X * X + X * Y + (Y * X + Y * Y) := by
    rw [Matrix.conjTranspose_add, hX.eq, hY.eq]
    noncomm_ring
  rw [frobSq, h1]
  simp only [Matrix.trace_add, Complex.add_re]
  have h2 : (Matrix.trace (Y * X)).re = (Matrix.trace (X * Y)).re := by
    rw [Matrix.trace_mul_comm]
  rw [frobSq, frobSq, hX.eq, hY.eq, rtrace, h2]
  ring

omit [DecidableEq n] in
/-- The basic "test matrix" bound: `‖X‖² ≥ 2⟨X,T⟩ - ‖T‖²`. -/
lemma two_rtrace_sub_frobSq_le {X T : Matrix n n ℂ} (hX : X.IsHermitian) (hT : T.IsHermitian) :
    2 * rtrace (X * T) - frobSq T ≤ frobSq X := by
  have hnT : (-T).IsHermitian := hT.neg
  have h1 : frobSq (X + (-T)) = frobSq X + 2 * rtrace (X * (-T)) + frobSq (-T) :=
    frobSq_add_of_isHermitian hX hnT
  have h2 : rtrace (X * (-T)) = -rtrace (X * T) := by
    rw [Matrix.mul_neg, rtrace, rtrace, Matrix.trace_neg]
    simp
  have h3 : frobSq (-T) = frobSq T := by
    rw [frobSq, frobSq, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have h4 := frobSq_nonneg (X + (-T))
  rw [h1, h2, h3] at h4
  linarith

omit [DecidableEq n] in
/-- If `S` is Hermitian and `X` is positive semidefinite then `Re tr (X * S * S) ≥ 0`. -/
lemma rtrace_mul_sq_nonneg {X S : Matrix n n ℂ} (hX : X.PosSemidef) (hS : S.IsHermitian) :
    0 ≤ rtrace (X * (S * S)) := by
  have h2 : Matrix.trace (X * (S * S)) = Matrix.trace (Sᴴ * X * S) := by
    rw [hS.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * S) S, Matrix.mul_assoc]
  have h3 : (Sᴴ * X * S).PosSemidef := hX.conjTranspose_mul_mul_same S
  have h4 := h3.trace_nonneg
  rw [rtrace, h2]
  simpa using (Complex.le_def.mp h4).1

/-! ### Properties of `conjD` -/

omit [Fintype n] in
lemma diagonal_ofReal_conjTranspose (f : n → ℝ) :
    (Matrix.diagonal (fun i => (f i : ℂ)))ᴴ = Matrix.diagonal (fun i => (f i : ℂ)) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h; simp [Matrix.conjTranspose_apply, Matrix.diagonal]
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal, h, Ne.symm h]

lemma conjD_mul (U : Matrix.unitaryGroup n ℂ) (f g : n → ℝ) :
    conjD U f * conjD U g = conjD U (fun i => f i * g i) := by
  have h : (star (U : Matrix n n ℂ)) * (U : Matrix n n ℂ) = 1 := U.2.1
  unfold conjD
  rw [show ((U : Matrix n n ℂ) * Matrix.diagonal (fun i => (f i : ℂ)) * (star U : Matrix n n ℂ)) *
      ((U : Matrix n n ℂ) * Matrix.diagonal (fun i => (g i : ℂ)) * (star U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (f i : ℂ)) *
        ((star U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
        Matrix.diagonal (fun i => (g i : ℂ)) * (star U : Matrix n n ℂ) by noncomm_ring, h]
  simp [Matrix.diagonal_mul_diagonal, Matrix.mul_assoc]

lemma conjD_add (U : Matrix.unitaryGroup n ℂ) (f g : n → ℝ) :
    conjD U f + conjD U g = conjD U (fun i => f i + g i) := by
  unfold conjD
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h]

lemma conjD_sub (U : Matrix.unitaryGroup n ℂ) (f g : n → ℝ) :
    conjD U f - conjD U g = conjD U (fun i => f i - g i) := by
  unfold conjD
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h]

lemma conjD_zero (U : Matrix.unitaryGroup n ℂ) : conjD U (fun _ => (0 : ℝ)) = 0 := by
  simp [conjD]

lemma conjD_const (U : Matrix.unitaryGroup n ℂ) (k : ℝ) :
    conjD U (fun _ => k) = (k : ℂ) • (1 : Matrix n n ℂ) := by
  have h : (U : Matrix n n ℂ) * (star (U : Matrix n n ℂ)) = 1 := U.2.2
  have hd : Matrix.diagonal (fun _ : n => (k : ℂ)) = (k : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [conjD, hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h]

lemma conjD_isHermitian (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) :
    (conjD U f).IsHermitian := by
  unfold Matrix.IsHermitian conjD
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, diagonal_ofReal_conjTranspose]
  simp [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose]

lemma conjD_posSemidef (U : Matrix.unitaryGroup n ℂ) {f : n → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (conjD U f).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (f i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using (hf i)
  have h2 := hd.mul_mul_conjTranspose_same (B := (U : Matrix n n ℂ))
  rw [conjD]
  convert h2 using 2

lemma rtrace_conjD (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) :
    rtrace (conjD U f) = ∑ i, f i := by
  have h : (star (U : Matrix n n ℂ)) * (U : Matrix n n ℂ) = 1 := U.2.1
  rw [rtrace, conjD, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp

lemma frobSq_conjD (U : Matrix.unitaryGroup n ℂ) (f : n → ℝ) :
    frobSq (conjD U f) = ∑ i, (f i) ^ 2 := by
  rw [frobSq_of_isHermitian (conjD_isHermitian U f), conjD_mul, rtrace_conjD]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma spectral_conjD {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = conjD hA.eigenvectorUnitary hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/-- Positive semidefinite matrices have nonnegative real trace against a `conjD` with
nonnegative weights. -/
lemma rtrace_mul_conjD_nonneg {X : Matrix n n ℂ} (hX : X.PosSemidef)
    (U : Matrix.unitaryGroup n ℂ) {f : n → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ rtrace (X * conjD U f) := by
  have hsplit : conjD U f = conjD U (fun i => Real.sqrt (f i)) * conjD U (fun i => Real.sqrt (f i)) := by
    rw [conjD_mul]
    congr 1
    funext i
    exact (Real.mul_self_sqrt (hf i)).symm
  rw [hsplit]
  exact rtrace_mul_sq_nonneg hX (conjD_isHermitian U _)

/-! ### The two halves of the argument -/

/-- With `Π` the spectral projection onto the range of `P` (scaled by `c/2`) as test matrix,
`frobSq (P - R) ≥ c * rtrace P - c * rtrace R - (c²/4) * rank P` for positive semidefinite
`P` and `R`. -/
lemma frobSq_sub_psd_lower {P R : Matrix n n ℂ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c * rtrace R - (c ^ 2 / 4) * (P.rank : ℝ) ≤ frobSq (P - R) := by
  set hPh := hP.isHermitian with hPh_def
  set U := hPh.eigenvectorUnitary with hU
  set lam := hPh.eigenvalues with hlam
  set ind : n → ℝ := fun i => if lam i = 0 then 0 else c / 2 with hind
  set comp : n → ℝ := fun i => if lam i = 0 then c / 2 else 0 with hcomp
  have hPsp : P = conjD U lam := spectral_conjD hPh
  set T := conjD U ind with hT
  have hfrobT : frobSq T = (c ^ 2 / 4) * (P.rank : ℝ) := by
    rw [hT, frobSq_conjD, hPh.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [show (fun i => (ind i) ^ 2) = (fun i => if lam i ≠ 0 then (c / 2) ^ 2 else 0) by
      funext i; by_cases h : lam i = 0 <;> simp [hind, h]]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]
    simp only [hlam]
    ring
  have hPT : rtrace (P * T) = (c / 2) * rtrace P := by
    rw [hPsp, hT, conjD_mul, rtrace_conjD, rtrace_conjD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : lam i = 0
    · simp [hind, h]
    · simp only [hind, if_neg h]; ring
  have hRT : rtrace (R * T) ≤ (c / 2) * rtrace R := by
    have hsum : T + conjD U comp = ((c / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
      rw [hT, conjD_add, ← conjD_const U (c / 2)]
      congr 1
      funext i
      by_cases h : lam i = 0 <;> simp [hind, hcomp, h]
    have h1 : rtrace (R * (T + conjD U comp)) = rtrace (R * T) + rtrace (R * conjD U comp) := by
      rw [Matrix.mul_add, rtrace_add]
    rw [hsum, rtrace_smul_one_mul] at h1
    have h2 : 0 ≤ rtrace (R * conjD U comp) := by
      refine rtrace_mul_conjD_nonneg hR U (fun i => ?_)
      by_cases h : lam i = 0
      · simp only [hcomp, if_pos h]; linarith
      · simp [hcomp, h]
    linarith
  have hkey :=
    two_rtrace_sub_frobSq_le (hP.isHermitian.sub hR.isHermitian) (conjD_isHermitian U ind)
  rw [← hT] at hkey
  have hexp : rtrace ((P - R) * T) = rtrace (P * T) - rtrace (R * T) := by
    rw [Matrix.sub_mul, rtrace_sub]
  rw [hexp, hfrobT] at hkey
  linarith

/-- The main inequality. -/
theorem rank_trace_ineq {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) {r b : ℝ}
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex Q : ℝ) ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  set Uq := hQ.eigenvectorUnitary with hUq
  set mu := hQ.eigenvalues with hmu
  set fpos : Fin d → ℝ := fun i => max (mu i) 0 with hfpos
  set fneg : Fin d → ℝ := fun i => max (-(mu i)) 0 with hfneg
  set Qpos := conjD Uq fpos with hQpos
  set Qneg := conjD Uq fneg with hQneg
  have hQposPSD : Qpos.PosSemidef := conjD_posSemidef Uq (fun i => le_max_right _ _)
  have hQnegPSD : Qneg.PosSemidef := conjD_posSemidef Uq (fun i => le_max_right _ _)
  have hQsplit : Q = Qpos - Qneg := by
    rw [hQpos, hQneg, conjD_sub]
    rw [show (fun i => fpos i - fneg i) = mu by
      funext i; simp only [hfpos, hfneg]; rcases le_or_gt (mu i) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h.le, max_eq_right (by linarith)]; ring]
    exact spectral_conjD hQ
  have hsplit2 : P + Q = (P - Qneg) + Qpos := by rw [hQsplit]; abel
  have hherm : (P - Qneg).IsHermitian := hP.isHermitian.sub hQnegPSD.isHermitian
  have hexp : frobSq (P + Q)
      = frobSq (P - Qneg) + 2 * rtrace ((P - Qneg) * Qpos) + frobSq Qpos := by
    rw [hsplit2, frobSq_add_of_isHermitian hherm hQposPSD.isHermitian]
  have hcross : 0 ≤ rtrace ((P - Qneg) * Qpos) := by
    have h0 : Qneg * Qpos = 0 := by
      rw [hQneg, hQpos, conjD_mul]
      rw [show (fun i => fneg i * fpos i) = (fun _ => (0 : ℝ)) by
        funext i; simp only [hfpos, hfneg]; rcases le_or_gt (mu i) 0 with h | h
        · rw [max_eq_right h]; ring
        · rw [max_eq_right (by linarith : -(mu i) ≤ 0)]; ring]
      exact conjD_zero Uq
    have h1 : rtrace ((P - Qneg) * Qpos) = rtrace (P * Qpos) - rtrace (Qneg * Qpos) := by
      rw [Matrix.sub_mul, rtrace_sub]
    rw [h1, h0, rtrace_zero, sub_zero, hQpos]
    exact rtrace_mul_conjD_nonneg hP Uq (fun i => le_max_right _ _)
  have hposIndex : (posIndex Q : ℝ) = ((Finset.univ.filter (fun i => 0 < mu i)).card : ℝ) := by
    rw [posIndex, dif_pos hQ]
  have hrtraceQ : rtrace Q = ∑ i, mu i := by
    conv_lhs => rw [spectral_conjD hQ]
    rw [rtrace_conjD]
  have hrtraceQneg : rtrace Qneg = ∑ i, fneg i := by rw [hQneg, rtrace_conjD]
  have hQposLower : 2 * c * (rtrace Q + rtrace Qneg) - c ^ 2 * (posIndex Q : ℝ) ≤ frobSq Qpos := by
    rw [hQpos, frobSq_conjD, hposIndex, hrtraceQ, hrtraceQneg]
    have hsplitsum : (∑ i, mu i) + (∑ i, fneg i) = ∑ i, fpos i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hfpos, hfneg]
      rcases le_or_gt (mu i) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h.le, max_eq_right (by linarith)]; ring
    have hcard : ((Finset.univ.filter (fun i => 0 < mu i)).card : ℝ)
        = ∑ i, (if 0 < mu i then (1 : ℝ) else 0) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero]
      simp
    rw [hsplitsum, hcard, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [hfpos]
    rcases le_or_gt (mu i) 0 with h | h
    · rw [max_eq_right h, if_neg (by linarith)]; ring_nf; positivity
    · rw [max_eq_left h.le, if_pos h]; nlinarith [sq_nonneg (mu i - c)]
  have hmain := frobSq_sub_psd_lower hP hQnegPSD hc
  have hQnegNonneg : 0 ≤ rtrace Qneg := by
    rw [hrtraceQneg]
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  have hrank : (c ^ 2 / 4) * (P.rank : ℝ) ≤ (c ^ 2 / 4) * r :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have hbb : c ^ 2 * (posIndex Q : ℝ) ≤ c ^ 2 * b :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  linarith [mul_nonneg hc.le hQnegNonneg]

/-- The specialization at `c = 2`. -/
theorem rank_trace_ineq_two {d : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) {r b : ℝ}
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex Q : ℝ) ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  nlinarith [this]

end LinAlg
end Zeta23Redux

