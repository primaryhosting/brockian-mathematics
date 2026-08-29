/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Statement: The rank-trace inequality (Lemma 3.2, the new ingredient). Let P, Q be Hermitian complex matrices of size Fin d with P positive semidefinite, rank P <= r, and posIndex Q <= b (b strictly positive eigenvalues of Q). Write rtrace X = Re (trace X) and frobSq X = Re (trace (Xᴴ * X)). Prove that for every real c > 0, c * rtrace P - (c^2/4) * r + 2 * c * rtrace Q - c^2 * b <= frobSq (P + Q). In parti...
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/
noncomputable def rtrace (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace X).re

/-- The squared Frobenius norm `Re tr (Xᴴ * X)` of a matrix. -/
noncomputable def frobSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity). -/
noncomputable def posIndex {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) : ℕ :=
  Fintype.card {i // 0 < hQ.eigenvalues i}

@[simp] lemma rtrace_zero : rtrace (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by simp [rtrace]

lemma rtrace_add (X Y : Matrix (Fin d) (Fin d) ℂ) : rtrace (X + Y) = rtrace X + rtrace Y := by
  simp [rtrace]

lemma rtrace_sub (X Y : Matrix (Fin d) (Fin d) ℂ) : rtrace (X - Y) = rtrace X - rtrace Y := by
  simp [rtrace]

lemma rtrace_mul_comm (X Y : Matrix (Fin d) (Fin d) ℂ) : rtrace (X * Y) = rtrace (Y * X) := by
  unfold rtrace; rw [Matrix.trace_mul_comm]

lemma rtrace_rsmul (t : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    rtrace ((t : ℂ) • X) = t * rtrace X := by
  simp [rtrace]

lemma frobSq_rsmul (t : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    frobSq ((t : ℂ) • X) = t ^ 2 * frobSq X := by
  simp only [frobSq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, RCLike.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma isHermitian_rsmul {X : Matrix (Fin d) (Fin d) ℂ} (t : ℝ) (hX : X.IsHermitian) :
    (((t : ℂ)) • X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hX.eq]
  simp

/-- The real part of the trace of a positive semidefinite matrix is nonnegative. -/
lemma rtrace_nonneg_of_posSemidef {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) :
    0 ≤ rtrace X := by
  simpa [rtrace] using (Complex.le_def.mp hX.trace_nonneg).1

lemma frobSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ frobSq X :=
  rtrace_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X)

lemma frobSq_add_herm {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + frobSq Y + 2 * rtrace (X * Y) := by
  simp only [frobSq, Matrix.conjTranspose_add, hX.eq, hY.eq, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re, rtrace]
  rw [Matrix.trace_mul_comm Y X]
  ring

lemma frobSq_sub_herm {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X - Y) = frobSq X + frobSq Y - 2 * rtrace (X * Y) := by
  simp only [frobSq, Matrix.conjTranspose_sub, hX.eq, hY.eq, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re, rtrace]
  rw [Matrix.trace_mul_comm Y X]
  ring

/-- The basic scalar inequality `‖X‖_F² ≥ 2 Re tr (X M) - ‖M‖_F²`, coming from
`‖X - M‖_F² ≥ 0`.  This is the matrix form of `x² ≥ 2 m x - m²`. -/
lemma quad_bound {X M : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hM : M.IsHermitian) :
    2 * rtrace (X * M) - frobSq M ≤ frobSq X := by
  have h0 : 0 ≤ frobSq (X - M) := frobSq_nonneg _
  rw [frobSq_sub_herm hX hM] at h0
  linarith

/-! ## Spectral (functional) calculus for Hermitian matrices -/

variable {A : Matrix (Fin d) (Fin d) ℂ}

/-- `specM hA f` is the Hermitian matrix obtained by applying the real function `f` to the
eigenvalues of the Hermitian matrix `A`. -/
noncomputable def specM (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ

lemma unit_star_mul (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact UnitaryGroup.star_mul_self hA.eigenvectorUnitary

lemma unit_mul_star (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
  mul_eq_one_comm.mp (unit_star_mul hA)

lemma specM_id (hA : A.IsHermitian) : specM hA id = A := by
  rw [specM]
  conv_rhs => rw [hA.spectral_theorem]
  simp [conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]

lemma specM_congr (hA : A.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hA.eigenvalues i) = g (hA.eigenvalues i)) : specM hA f = specM hA g := by
  unfold specM
  rw [funext (fun i => congrArg (Complex.ofReal) (h i))]

lemma specM_mul (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specM hA f * specM hA g = specM hA (fun x => f x * g x) := by
  simp only [specM, Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ),
    unit_star_mul, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  simp

lemma specM_sub (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specM hA f - specM hA g = specM hA (fun x => f x - g x) := by
  simp only [specM, ← Matrix.sub_mul, ← Matrix.mul_sub]
  norm_num

lemma specM_one (hA : A.IsHermitian) : specM hA (fun _ => 1) = 1 := by
  simp only [specM, Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one]
  exact unit_mul_star hA

lemma specM_zero (hA : A.IsHermitian) : specM hA (fun _ => 0) = 0 := by
  simp [specM]

lemma specM_herm (hA : A.IsHermitian) (f : ℝ → ℝ) : (specM hA f).IsHermitian := by
  unfold Matrix.IsHermitian specM
  simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Pi.star_def, Matrix.mul_assoc]

lemma specM_psd (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (specM hA f).PosSemidef := by
  have h : (Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using Complex.zero_le_real.mpr (hf i)
  simpa [specM, Matrix.mul_assoc] using h.mul_mul_conjTranspose_same
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)

lemma specM_trace (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (specM hA f) = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [specM, Matrix.trace_mul_cycle, unit_star_mul, Matrix.one_mul, Matrix.trace_diagonal]
  push_cast
  ring

lemma rtrace_specM (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtrace (specM hA f) = ∑ i, f (hA.eigenvalues i) := by
  simp [rtrace, specM_trace]

lemma frobSq_specM (hA : A.IsHermitian) (f : ℝ → ℝ) :
    frobSq (specM hA f) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  have h : frobSq (specM hA f) = rtrace (specM hA f * specM hA f) := by
    unfold frobSq rtrace
    rw [(specM_herm hA f).eq]
  rw [h, specM_mul, rtrace_specM]
  simp [sq]

lemma rtrace_eq_sum_eigenvalues (hA : A.IsHermitian) : rtrace A = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [← specM_id hA]
  rw [rtrace_specM]
  rfl

/-- The real trace of the product of two positive semidefinite matrices is nonnegative. -/
lemma rtrace_mul_nonneg {B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ rtrace (A * B) := by
  set R := specM hA.1 Real.sqrt with hRdef
  have hRR : R * R = A := by
    rw [hRdef, specM_mul,
      specM_congr hA.1 (g := id) (fun i => by
        simpa using Real.mul_self_sqrt (hA.eigenvalues_nonneg i))]
    exact specM_id hA.1
  have hRh : R.IsHermitian := specM_herm hA.1 _
  calc (0 : ℝ) ≤ rtrace (Rᴴ * B * R) := rtrace_nonneg_of_posSemidef (hB.conjTranspose_mul_mul_same R)
    _ = rtrace (A * B) := by
        rw [hRh.eq, rtrace_mul_comm (R * B) R, ← Matrix.mul_assoc, hRR]

/-! ## Spectral projections -/

section Projections

variable (hA : A.IsHermitian)

/-- The orthogonal projection onto the range of a Hermitian matrix (the support projection). -/
noncomputable def suppProj (hA : A.IsHermitian) : Matrix (Fin d) (Fin d) ℂ :=
  specM hA (fun x => if x = 0 then 0 else 1)

/-- The orthogonal projection onto the sum of the eigenspaces with positive eigenvalue. -/
noncomputable def posProj (hA : A.IsHermitian) : Matrix (Fin d) (Fin d) ℂ :=
  specM hA (fun x => if 0 < x then 1 else 0)

lemma suppProj_herm : (suppProj hA).IsHermitian := specM_herm _ _

lemma posProj_herm : (posProj hA).IsHermitian := specM_herm _ _

lemma mul_suppProj : A * suppProj hA = A := by
  have h : A * suppProj hA = specM hA id * suppProj hA := by rw [specM_id]
  rw [h, suppProj, specM_mul,
    specM_congr hA (g := id) (fun i => by
      by_cases h : hA.eigenvalues i = 0 <;> simp [h])]
  exact specM_id hA

lemma one_sub_suppProj_psd : ((1 : Matrix (Fin d) (Fin d) ℂ) - suppProj hA).PosSemidef := by
  rw [← specM_one hA, suppProj, specM_sub]
  exact specM_psd hA _ (fun i => by by_cases h : hA.eigenvalues i = 0 <;> simp [h])

lemma frobSq_suppProj : frobSq (suppProj hA) = (A.rank : ℝ) := by
  rw [suppProj, frobSq_specM, hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  simp [Finset.sum_ite, Finset.filter_not]

lemma frobSq_posProj : frobSq (posProj hA) = (posIndex hA : ℝ) := by
  rw [posProj, frobSq_specM, posIndex, Fintype.card_subtype]
  simp

end Projections

/-! ## The rank-trace inequality -/

/-- **Rank-trace inequality** (Lemma 3.2).  Let `P` and `Q` be Hermitian complex matrices of
size `d`, with `P` positive semidefinite of rank at most `r`, and with `Q` having at most `b`
strictly positive eigenvalues.  Then for every `c > 0`,
`c * rtrace P - (c²/4) * r + 2 * c * rtrace Q - c² * b ≤ frobSq (P + Q)`. -/
theorem rank_trace_ineq {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) {r b : ℝ}
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex hQ : ℝ) ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  have hP1 : P.IsHermitian := hP.1
  -- the Jordan decomposition `Q = Qp - Qm` into positive and negative parts
  set Qp : Matrix (Fin d) (Fin d) ℂ := specM hQ (fun x => max x 0) with hQpdef
  set Qm : Matrix (Fin d) (Fin d) ℂ := specM hQ (fun x => max (-x) 0) with hQmdef
  have hQp_h : Qp.IsHermitian := specM_herm _ _
  have hQm_h : Qm.IsHermitian := specM_herm _ _
  have hQp_psd : Qp.PosSemidef := specM_psd _ _ (fun i => le_max_right _ _)
  have hQm_psd : Qm.PosSemidef := specM_psd _ _ (fun i => le_max_right _ _)
  have hQ_eq : Qp - Qm = Q := by
    rw [hQpdef, hQmdef, specM_sub,
      specM_congr hQ (g := id) (fun i => by
        rcases le_total (hQ.eigenvalues i) 0 with h | h
        · simp [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -hQ.eigenvalues i)]
        · simp [max_eq_left h, max_eq_right (by linarith : -hQ.eigenvalues i ≤ 0)])]
    exact specM_id hQ
  have hQmQp : Qm * Qp = 0 := by
    rw [hQpdef, hQmdef, specM_mul,
      specM_congr hQ (g := fun _ => 0) (fun i => by
        rcases le_total (hQ.eigenvalues i) 0 with h | h
        · simp [max_eq_right h]
        · simp [max_eq_right (by linarith : -hQ.eigenvalues i ≤ 0)])]
    exact specM_zero hQ
  have hQpPos : Qp * posProj hQ = Qp := by
    rw [hQpdef, posProj, specM_mul]
    exact specM_congr hQ (fun i => by
      rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
      · simp [h]
      · simp [not_lt.mpr h, max_eq_right h])
  -- traces
  have hrQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [← hQ_eq, rtrace_sub]
  have hQm_tr : 0 ≤ rtrace Qm := rtrace_nonneg_of_posSemidef hQm_psd
  -- Step 1: the `P` part, with the interaction term `tr (P Qm)` absorbed
  have key1 : c * rtrace P - c * rtrace Qm - (c ^ 2 / 4) * (P.rank : ℝ) ≤ frobSq (P - Qm) := by
    have hqb := quad_bound (X := P - Qm) (M := ((c / 2 : ℝ) : ℂ) • suppProj hP1)
      (hP1.sub hQm_h) (isHermitian_rsmul _ (suppProj_herm hP1))
    have hmul : (P - Qm) * (((c / 2 : ℝ) : ℂ) • suppProj hP1)
        = ((c / 2 : ℝ) : ℂ) • (P * suppProj hP1 - Qm * suppProj hP1) := by
      rw [Matrix.mul_smul, Matrix.sub_mul]
    have hinter : rtrace (Qm * suppProj hP1) ≤ rtrace Qm := by
      have h0 : 0 ≤ rtrace (Qm * (1 - suppProj hP1)) :=
        rtrace_mul_nonneg hQm_psd (one_sub_suppProj_psd hP1)
      rw [Matrix.mul_sub, Matrix.mul_one, rtrace_sub] at h0
      linarith
    rw [hmul, rtrace_rsmul, rtrace_sub, mul_suppProj, frobSq_rsmul, frobSq_suppProj] at hqb
    have hc2 : 0 ≤ c / 2 := by linarith
    nlinarith [hqb, hinter, mul_le_mul_of_nonneg_left hinter hc2]
  -- Step 2: the positive part of `Q`
  have key2 : 2 * c * rtrace Qp - c ^ 2 * (posIndex hQ : ℝ) ≤ frobSq Qp := by
    have hqb := quad_bound (X := Qp) (M := ((c : ℝ) : ℂ) • posProj hQ)
      hQp_h (isHermitian_rsmul _ (posProj_herm hQ))
    rw [Matrix.mul_smul, hQpPos, rtrace_rsmul, frobSq_rsmul, frobSq_posProj] at hqb
    linarith
  -- Step 3: expand `frobSq (P + Q)`
  have hsplit : P + Q = (P - Qm) + Qp := by
    rw [← hQ_eq]; abel
  have hcross : 0 ≤ rtrace ((P - Qm) * Qp) := by
    rw [Matrix.sub_mul, rtrace_sub, hQmQp, rtrace_zero, sub_zero]
    exact rtrace_mul_nonneg hP hQp_psd
  have hexp : frobSq (P + Q) = frobSq (P - Qm) + frobSq Qp + 2 * rtrace ((P - Qm) * Qp) := by
    rw [hsplit, frobSq_add_herm (hP1.sub hQm_h) hQp_h]
  -- combine
  have h1 : 0 ≤ (c ^ 2 / 4) * (r - (P.rank : ℝ)) := by
    have : 0 ≤ r - (P.rank : ℝ) := by linarith
    positivity
  have h2 : 0 ≤ c ^ 2 * (b - (posIndex hQ : ℝ)) := by
    have : 0 ≤ b - (posIndex hQ : ℝ) := by linarith
    positivity
  have h3 : 0 ≤ c * rtrace Qm := mul_nonneg hc.le hQm_tr
  rw [hexp, hrQ]
  nlinarith [key1, key2, hcross, h1, h2, h3]

/-- The specialization of `rank_trace_ineq` at `c = 2`. -/
theorem rank_trace_ineq_two {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) {r b : ℝ}
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex hQ : ℝ) ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have h := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  norm_num at h
  linarith

end Zeta23Redux.LinAlg

