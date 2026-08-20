/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Lean requires `import` to precede any module docstring, so the header is
repeated as a module docstring immediately after the import below.)
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
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

/-- Square complex matrices of size `Fin d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ}

/-- The real part of the trace. -/
noncomputable def rtrace (X : Mat d) : ℝ := (Matrix.trace X).re

/-- The squared Frobenius norm, `Re tr (Xᴴ X)`. -/
noncomputable def frobSq (X : Mat d) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The real trace pairing `Re tr (X Y)`; on Hermitian matrices this is the
Frobenius (Hilbert–Schmidt) inner product. -/
noncomputable def rinner (X Y : Mat d) : ℝ := (Matrix.trace (X * Y)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix,
counted with multiplicity. -/
noncomputable def posIndex {Q : Mat d} (hQ : Q.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hQ.eigenvalues i).card

/-! ### Basic properties of the trace pairing -/

lemma rinner_eq_rtrace_mul (X Y : Mat d) : rinner X Y = rtrace (X * Y) := rfl

lemma rtrace_sub (X Y : Mat d) : rtrace (X - Y) = rtrace X - rtrace Y := by
  simp [rtrace]

lemma rinner_one_right (X : Mat d) : rinner X 1 = rtrace X := by
  simp [rinner, rtrace]

lemma rinner_comm (X Y : Mat d) : rinner X Y = rinner Y X := by
  rw [rinner, rinner, Matrix.trace_mul_comm]

lemma rinner_add_left (X Y Z : Mat d) :
    rinner (X + Y) Z = rinner X Z + rinner Y Z := by
  simp [rinner, Matrix.add_mul]

lemma rinner_sub_left (X Y Z : Mat d) :
    rinner (X - Y) Z = rinner X Z - rinner Y Z := by
  simp [rinner, Matrix.sub_mul]

lemma rinner_add_right (X Y Z : Mat d) :
    rinner X (Y + Z) = rinner X Y + rinner X Z := by
  simp [rinner, Matrix.mul_add]

lemma rinner_sub_right (X Y Z : Mat d) :
    rinner X (Y - Z) = rinner X Y - rinner X Z := by
  simp [rinner, Matrix.mul_sub]

lemma rinner_smul_right (t : ℝ) (X Y : Mat d) :
    rinner X ((t : ℂ) • Y) = t * rinner X Y := by
  simp [rinner, Matrix.trace_smul]

lemma frobSq_nonneg (X : Mat d) : 0 ≤ frobSq X := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  rw [Complex.le_def] at h
  simpa [frobSq] using h.1

lemma frobSq_eq_rinner {X : Mat d} (hX : X.IsHermitian) : frobSq X = rinner X X := by
  rw [frobSq, rinner, hX.eq]

lemma smul_isHermitian {N : Mat d} (hN : N.IsHermitian) (t : ℝ) :
    ((t : ℂ) • N).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hN.eq]
  simp

lemma frobSq_add {X Y : Mat d} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + 2 * rinner X Y + frobSq Y := by
  rw [frobSq_eq_rinner (hX.add hY), frobSq_eq_rinner hX, frobSq_eq_rinner hY,
    rinner_add_left, rinner_add_right, rinner_add_right, rinner_comm Y X]
  ring

/-- Young's inequality for the Frobenius inner product. -/
lemma two_mul_rinner_le {M N : Mat d} (hM : M.IsHermitian) (hN : N.IsHermitian) (t : ℝ) :
    2 * t * rinner M N ≤ frobSq M + t ^ 2 * frobSq N := by
  have hS := smul_isHermitian hN t
  have h0 := frobSq_nonneg (M - (t : ℂ) • N)
  rw [frobSq_eq_rinner (hM.sub hS)] at h0
  simp only [rinner_sub_left, rinner_sub_right, rinner_smul_right,
    rinner_comm ((t : ℂ) • N) M, rinner_comm ((t : ℂ) • N) N] at h0
  rw [frobSq_eq_rinner hM, frobSq_eq_rinner hN]
  nlinarith [h0]

/-- The trace pairing of a positive semidefinite matrix with a square of a Hermitian
matrix is nonnegative. -/
lemma rinner_nonneg_conj {A S : Mat d} (hA : A.PosSemidef) (hS : S.IsHermitian) :
    0 ≤ rinner A (S * S) := by
  have h : (Sᴴ * A * S).PosSemidef := hA.conjTranspose_mul_mul_same S
  have hnn := h.trace_nonneg
  rw [Complex.le_def] at hnn
  have h2 : Matrix.trace (A * (S * S)) = Matrix.trace (Sᴴ * A * S) := by
    calc Matrix.trace (A * (S * S)) = Matrix.trace ((A * S) * S) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (S * (A * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Sᴴ * A * S) := by rw [hS.eq, Matrix.mul_assoc]
  simpa [rinner, h2] using hnn.1

/-! ### Conjugated diagonal matrices -/

/-- `cdiag U f = U * diagonal f * Uᴴ`. -/
noncomputable def cdiag (U : Mat d) (f : Fin d → ℝ) : Mat d :=
  U * Matrix.diagonal (fun i => (f i : ℂ)) * Uᴴ

variable {U : Mat d} {f g : Fin d → ℝ}

lemma cdiag_isHermitian (U : Mat d) (f : Fin d → ℝ) : (cdiag U f).IsHermitian := by
  unfold Matrix.IsHermitian cdiag
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose]
  simp [Matrix.mul_assoc, Pi.star_def, Complex.conj_ofReal]

lemma cdiag_mul (hU : Uᴴ * U = 1) (f g : Fin d → ℝ) :
    cdiag U f * cdiag U g = cdiag U (fun i => f i * g i) := by
  simp only [cdiag, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal fun i => ((f i : ℝ) : ℂ)), Matrix.diagonal_mul_diagonal]
  simp

lemma cdiag_sub (U : Mat d) (f g : Fin d → ℝ) :
    cdiag U f - cdiag U g = cdiag U (fun i => f i - g i) := by
  have h : (Matrix.diagonal fun i => (((f i - g i : ℝ)) : ℂ))
      = Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))
        - Matrix.diagonal (fun i => ((g i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  simp only [cdiag, h, Matrix.mul_sub, Matrix.sub_mul]

lemma cdiag_add (U : Mat d) (f g : Fin d → ℝ) :
    cdiag U f + cdiag U g = cdiag U (fun i => f i + g i) := by
  have h : (Matrix.diagonal fun i => (((f i + g i : ℝ)) : ℂ))
      = Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))
        + Matrix.diagonal (fun i => ((g i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  simp only [cdiag, h, Matrix.mul_add, Matrix.add_mul]

lemma cdiag_zero (U : Mat d) : cdiag U (fun _ => (0 : ℝ)) = 0 := by
  simp [cdiag]

lemma cdiag_one (hU : U * Uᴴ = 1) : cdiag U (fun _ => (1 : ℝ)) = 1 := by
  simp [cdiag, hU]

lemma cdiag_trace (hU : Uᴴ * U = 1) (f : Fin d → ℝ) :
    rtrace (cdiag U f) = ∑ i, f i := by
  simp only [cdiag, rtrace]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.trace_diagonal]
  simp

lemma cdiag_posSemidef (hf : ∀ i, 0 ≤ f i) : (cdiag U f).PosSemidef := by
  have hD : (Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using hf i
  simpa [cdiag, Matrix.mul_assoc] using hD.conjTranspose_mul_mul_same Uᴴ

lemma cdiag_frobSq (hU : Uᴴ * U = 1) (f : Fin d → ℝ) :
    frobSq (cdiag U f) = ∑ i, f i ^ 2 := by
  rw [frobSq_eq_rinner (cdiag_isHermitian U f), rinner, ← rtrace, cdiag_mul hU, cdiag_trace hU]
  simp [pow_two]

lemma sum_indicator_sq (p : Fin d → Prop) [DecidablePred p] :
    ∑ i, (if p i then (1 : ℝ) else 0) ^ 2 = ((Finset.univ.filter p).card : ℝ) := by
  simp [apply_ite (fun x : ℝ => x ^ 2), Finset.sum_boole]

/-- Spectral theorem, in the `cdiag` form. -/
lemma exists_cdiag {X : Mat d} (hX : X.IsHermitian) :
    ∃ U : Mat d, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ X = cdiag U hX.eigenvalues := by
  refine ⟨(hX.eigenvectorUnitary : Mat d), ?_, ?_, ?_⟩
  · have h := hX.eigenvectorUnitary.2.1
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  · have h := hX.eigenvectorUnitary.2.2
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  · conv_lhs => rw [hX.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, cdiag]
    rfl

/-! ### The main inequality -/

/-- **Rank-trace inequality** (Lemma 3.2). For `P` positive semidefinite of rank at most `r`
and `Q` Hermitian with at most `b` strictly positive eigenvalues, and every real `c > 0`:
`c ⬝ Re tr P - (c²/4)⬝r + 2c ⬝ Re tr Q - c²⬝b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {d r b : ℕ} {P Q : Mat d}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  obtain ⟨U, hU1, -, hQeq⟩ := exists_cdiag hQ
  obtain ⟨V, hV1, hV2, hPeq⟩ := exists_cdiag hP.isHermitian
  set nu : Fin d → ℝ := hQ.eigenvalues
  set mu : Fin d → ℝ := hP.isHermitian.eigenvalues
  set Qp : Mat d := cdiag U (fun i => max (nu i) 0) with hQpdef
  set Qm : Mat d := cdiag U (fun i => max (-(nu i)) 0) with hQmdef
  set Ep : Mat d := cdiag U (fun i => if 0 < nu i then (1 : ℝ) else 0) with hEpdef
  set Pp : Mat d := cdiag V (fun i => if mu i ≠ 0 then (1 : ℝ) else 0) with hPpdef
  set Ec : Mat d := cdiag V (fun i => if mu i ≠ 0 then (0 : ℝ) else 1) with hEcdef
  have hQpH : Qp.IsHermitian := cdiag_isHermitian _ _
  have hQmH : Qm.IsHermitian := cdiag_isHermitian _ _
  have hEpH : Ep.IsHermitian := cdiag_isHermitian _ _
  have hPpH : Pp.IsHermitian := cdiag_isHermitian _ _
  have hEcH : Ec.IsHermitian := cdiag_isHermitian _ _
  -- `Q = Qp - Qm` is the Jordan decomposition of `Q`
  have hQsplit : Q = Qp - Qm := by
    rw [hQpdef, hQmdef, cdiag_sub, hQeq]
    congr 1
    funext i
    rcases le_total 0 (nu i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(nu i) ≤ 0)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -(nu i))]; ring
  -- the positive and negative parts are orthogonal
  have hQpQm : rinner Qp Qm = 0 := by
    have hmul : Qp * Qm = 0 := by
      rw [hQpdef, hQmdef, cdiag_mul hU1]
      have h : (fun i => max (nu i) 0 * max (-(nu i)) 0) = fun _ => (0 : ℝ) := by
        funext i
        rcases le_total 0 (nu i) with h | h
        · rw [max_eq_right (by linarith : -(nu i) ≤ 0)]; ring
        · rw [max_eq_right h]; ring
      rw [h, cdiag_zero]
    rw [rinner_eq_rtrace_mul, hmul]
    simp [rtrace]
  -- `Ep` is the spectral projection onto the positive eigenvalues of `Q`
  have hQpEp : rinner Qp Ep = rtrace Qp := by
    have hmul : Qp * Ep = Qp := by
      rw [hQpdef, hEpdef, cdiag_mul hU1]
      congr 1
      funext i
      by_cases h : 0 < nu i
      · rw [if_pos h]; ring
      · rw [if_neg h, max_eq_right (by linarith [not_lt.mp h] : nu i ≤ 0)]; ring
    rw [rinner_eq_rtrace_mul, hmul]
  have hEpb : frobSq Ep ≤ (b : ℝ) := by
    rw [hEpdef, cdiag_frobSq hU1]
    rw [sum_indicator_sq (fun i => 0 < nu i)]
    exact_mod_cast hb
  -- `Pp` is the projection onto the range of `P`
  have hPPp : rinner P Pp = rtrace P := by
    have hmul : P * Pp = P := by
      rw [hPpdef, hPeq, cdiag_mul hV1]
      congr 1
      funext i
      by_cases h : mu i ≠ 0 <;> simp [h]
      · exact (not_not.mp h).symm
    rw [rinner_eq_rtrace_mul, hmul]
  have hPpr : frobSq Pp ≤ (r : ℝ) := by
    rw [hPpdef, cdiag_frobSq hV1]
    have h2 : (Finset.univ.filter fun i => mu i ≠ 0).card = P.rank := by
      rw [hP.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [sum_indicator_sq (fun i => mu i ≠ 0), h2]
    exact_mod_cast hr
  have hPpEc : Pp + Ec = 1 := by
    rw [hPpdef, hEcdef, cdiag_add]
    have h : (fun i => (if mu i ≠ 0 then (1 : ℝ) else 0) + (if mu i ≠ 0 then (0 : ℝ) else 1))
        = fun _ => (1 : ℝ) := by
      funext i; by_cases h : mu i ≠ 0 <;> simp [h]
    rw [h, cdiag_one hV2]
  have hEcEc : Ec * Ec = Ec := by
    rw [hEcdef, cdiag_mul hV1]
    congr 1
    funext i
    by_cases h : mu i ≠ 0 <;> simp [h]
  have hQmPSD : Qm.PosSemidef := cdiag_posSemidef (fun i => le_max_right _ _)
  have hQmEc : 0 ≤ rinner Qm Ec := by
    have h := rinner_nonneg_conj hQmPSD hEcH
    rwa [hEcEc] at h
  have hPQp : 0 ≤ rinner P Qp := by
    have hSS : (cdiag U (fun i => Real.sqrt (max (nu i) 0)))
        * (cdiag U (fun i => Real.sqrt (max (nu i) 0))) = Qp := by
      rw [cdiag_mul hU1, hQpdef]
      congr 1
      funext i
      exact Real.mul_self_sqrt (le_max_right _ _)
    have h := rinner_nonneg_conj hP (cdiag_isHermitian U (fun i => Real.sqrt (max (nu i) 0)))
    rwa [hSS] at h
  have hQmtr : 0 ≤ rtrace Qm := by
    rw [hQmdef, cdiag_trace hU1]
    exact Finset.sum_nonneg fun i _ => le_max_right _ _
  have htrQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [hQsplit, rtrace_sub]
  -- Step 1: drop the (nonnegative) interaction with the positive part
  have key1 : frobSq (P - Qm) + frobSq Qp ≤ frobSq (P + Q) := by
    have hsum : P + Q = (P - Qm) + Qp := by rw [hQsplit]; abel
    rw [hsum, frobSq_add (hP.isHermitian.sub hQmH) hQpH]
    have hnn : 0 ≤ rinner (P - Qm) Qp := by
      rw [rinner_sub_left, rinner_comm Qm Qp, hQpQm]
      linarith
    linarith
  -- Step 2: the bound for the positive part of `Q`
  have ineqA : 2 * c * rtrace Qp - c ^ 2 * (b : ℝ) ≤ frobSq Qp := by
    have h := two_mul_rinner_le hQpH hEpH c
    rw [hQpEp] at h
    nlinarith [sq_nonneg c]
  -- Step 3: the bound involving `P` and the negative part of `Q`
  have ineqB : c * rtrace P - (c ^ 2 / 4) * (r : ℝ) - 2 * c * rtrace Qm ≤ frobSq (P - Qm) := by
    have h := two_mul_rinner_le (hP.isHermitian.sub hQmH) hPpH (c / 2)
    have h1 : rinner (P - Qm) Pp = rtrace P - rinner Qm Pp := by
      rw [rinner_sub_left, hPPp]
    have h2 : rinner Qm Pp ≤ rtrace Qm := by
      have h3 : rinner Qm Pp + rinner Qm Ec = rtrace Qm := by
        rw [← rinner_add_right, hPpEc, rinner_one_right]
      linarith
    rw [h1] at h
    have h4 : c * rinner Qm Pp ≤ c * rtrace Qm := by
      exact mul_le_mul_of_nonneg_left h2 hc.le
    nlinarith [sq_nonneg c, hQmtr]
  rw [htrQ]
  linarith

/-- The rank-trace inequality specialized at `c = 2`. -/
theorem rank_trace_ineq_two {d r b : ℕ} {P Q : Mat d}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have h := rank_trace_ineq (r := r) (b := b) hP hQ hr hb (c := 2) (by norm_num)
  norm_num at h
  linarith

end Zeta23Redux.LinAlg

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

