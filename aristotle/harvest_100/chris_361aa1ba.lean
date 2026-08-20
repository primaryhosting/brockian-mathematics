/-
/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Rank–trace inequality (preprint Lemma 3.2):
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P+Q‖_F²`,
for `P` positive semidefinite of rank at most `r`, `Q` Hermitian with at most `b` positive
eigenvalues, and `c > 0`.

The proof does not use von Neumann's trace inequality; instead it uses the two orthogonal
projections `Pi` (onto the positive spectral subspace of `Q`) and `R` (onto the range of the
compression `(1 - Pi) P (1 - Pi)`), and the elementary estimate `0 ≤ ‖S - M‖_F²` for
`S = P + Q` and `M = c·Pi + (c/2)·R`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Zeta23Core

open Matrix
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/
noncomputable def frobSq (M : Matrix n n 𝕜) : ℝ := RCLike.re (Matrix.trace (Mᴴ * M))

/-- The positive index of a Hermitian matrix: the number of its positive eigenvalues. -/
noncomputable def posIndex {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Fintype.card {i // 0 < hQ.eigenvalues i}

/-! ## Functional calculus for Hermitian matrices (spectral functions) -/

/-- `specFun hM f` applies the real function `f` to the Hermitian matrix `M` through its
spectral decomposition. -/
noncomputable def specFun {M : Matrix n n 𝕜} (hM : M.IsHermitian) (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  (hM.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => ((f (hM.eigenvalues i) : ℝ) : 𝕜)) *
    (hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ

variable {M : Matrix n n 𝕜}

theorem eigenvectorUnitary_conjTranspose_mul (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ * (hM.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2

theorem eigenvectorUnitary_mul_conjTranspose (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix n n 𝕜) * (hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2

theorem specFun_mul (hM : M.IsHermitian) (f g : ℝ → ℝ) :
    specFun hM f * specFun hM g = specFun hM (fun x => f x * g x) := by
  simp only [specFun, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ),
    eigenvectorUnitary_conjTranspose_mul hM, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp

theorem specFun_one (hM : M.IsHermitian) : specFun hM (fun _ => 1) = 1 := by
  simp [specFun, eigenvectorUnitary_mul_conjTranspose hM]

theorem specFun_zero (hM : M.IsHermitian) : specFun hM (fun _ => 0) = 0 := by
  simp [specFun]

theorem specFun_id (hM : M.IsHermitian) : specFun hM id = M := by
  conv_rhs => rw [hM.spectral_theorem]
  simp [specFun, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]

theorem specFun_congr (hM : M.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hM.eigenvalues i) = g (hM.eigenvalues i)) : specFun hM f = specFun hM g := by
  simp only [specFun, h]

theorem specFun_isHermitian (hM : M.IsHermitian) (f : ℝ → ℝ) : (specFun hM f).IsHermitian := by
  unfold Matrix.IsHermitian specFun
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  simp [Matrix.mul_assoc, Pi.star_def, RCLike.star_def]

theorem specFun_posSemidef (hM : M.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hM.eigenvalues i)) :
    (specFun hM f).PosSemidef := by
  have h : specFun hM f = ((hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ)ᴴ *
      (Matrix.diagonal (fun i => ((f (hM.eigenvalues i) : ℝ) : 𝕜))) *
      (hM.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    simp [specFun]
  rw [h]
  refine Matrix.PosSemidef.conjTranspose_mul_mul_same ?_ _
  refine Matrix.PosSemidef.diagonal (Pi.le_def.mpr fun i => ?_)
  exact (RCLike.ofReal_nonneg (K := 𝕜)).mpr (hf i)

theorem specFun_neg (hM : M.IsHermitian) (f : ℝ → ℝ) :
    -(specFun hM f) = specFun hM (fun x => -f x) := by
  have hd : (Matrix.diagonal fun i => (((-f (hM.eigenvalues i)) : ℝ) : 𝕜))
      = -(Matrix.diagonal fun i => ((f (hM.eigenvalues i) : ℝ) : 𝕜)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  simp only [specFun, hd, Matrix.neg_mul, Matrix.mul_neg]

theorem specFun_add (hM : M.IsHermitian) (f g : ℝ → ℝ) :
    specFun hM f + specFun hM g = specFun hM (fun x => f x + g x) := by
  simp only [specFun, ← Matrix.add_mul, ← Matrix.mul_add]
  norm_num

theorem specFun_trace (hM : M.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (specFun hM f) = ∑ i, ((f (hM.eigenvalues i) : ℝ) : 𝕜) := by
  simp only [specFun]
  rw [Matrix.trace_mul_cycle, eigenvectorUnitary_conjTranspose_mul hM, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- The real part of the trace of a spectral projection is the number of eigenvalues selected. -/
theorem re_trace_specFun_indicator (hM : M.IsHermitian) (p : ℝ → Prop) [DecidablePred p] :
    RCLike.re (Matrix.trace (specFun hM (fun x => if p x then 1 else 0)))
      = (Fintype.card {i // p (hM.eigenvalues i)} : ℝ) := by
  rw [specFun_trace, map_sum]
  simp only [RCLike.ofReal_re]
  rw [Finset.sum_boole, Fintype.card_subtype]

/-! ## Trace positivity toolbox -/

theorem posSemidef_re_trace_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    0 ≤ RCLike.re A.trace := (RCLike.nonneg_iff.mp hA.trace_nonneg).1

theorem re_trace_conj_nonpos {N A : Matrix n n 𝕜} (hN : (-N).PosSemidef) :
    RCLike.re (Matrix.trace (Aᴴ * N * A)) ≤ 0 := by
  have h := posSemidef_re_trace_nonneg (hN.conjTranspose_mul_mul_same A)
  have h2 : Aᴴ * (-N) * A = -(Aᴴ * N * A) := by simp
  rw [h2] at h
  simp only [Matrix.trace_neg, map_neg] at h
  linarith

theorem frobSq_nonneg (A : Matrix n n 𝕜) : 0 ≤ frobSq A :=
  posSemidef_re_trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self A)

theorem frobSq_sub {S T : Matrix n n 𝕜} (hS : S.IsHermitian) (hT : T.IsHermitian) :
    frobSq (S - T) = frobSq S - 2 * RCLike.re (Matrix.trace (S * T)) + frobSq T := by
  simp only [frobSq, Matrix.conjTranspose_sub, hS.eq, hT.eq, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, map_sub]
  rw [Matrix.trace_mul_comm T S]
  ring

theorem conjTranspose_real_smul (a : ℝ) (A : Matrix n n 𝕜) : (a • A)ᴴ = a • Aᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply, RCLike.real_smul_eq_coe_mul, RCLike.conj_ofReal]

/-! ## The core inequality, given a suitable pair of orthogonal projections -/

/-- The main estimate, assuming the existence of two orthogonal projections `Pi` (capturing the
positive part of `Q`) and `R` (capturing the part of the range of `P` orthogonal to `Pi`). -/
theorem trace_ineq_of_projections {P Q Pi R : Matrix n n 𝕜} {r b : ℕ} {c : ℝ}
    (hc : 0 < c) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hPih : Pi.IsHermitian) (hPi2 : Pi * Pi = Pi)
    (hRh : R.IsHermitian) (hR2 : R * R = R)
    (hPiR : Pi * R = 0) (hRPi : R * Pi = 0)
    (htPi : RCLike.re Pi.trace ≤ b) (htR : RCLike.re R.trace ≤ r)
    (hNSD : (-((1 - Pi) * Q * (1 - Pi))).PosSemidef)
    (hKE : ((1 - Pi) * P * (1 - Pi)) * (1 - Pi - R) = 0) :
    c * RCLike.re P.trace - c ^ 2 / 4 * r + 2 * c * RCLike.re Q.trace - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  obtain ⟨E, hE⟩ : ∃ E : Matrix n n 𝕜, E = 1 - Pi - R := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n 𝕜, S = P + Q := ⟨_, rfl⟩
  have hSh : S.IsHermitian := by rw [hS]; exact hP.1.add hQ
  have hEh : E.IsHermitian := by
    rw [Matrix.IsHermitian, hE]
    simp [Matrix.conjTranspose_sub, hPih.eq, hRh.eq]
  -- orthogonality relations between the three projections
  have hEPi : E * Pi = 0 := by rw [hE]; simp [Matrix.sub_mul, hPi2, hRPi]
  have hPiE : Pi * E = 0 := by rw [hE]; simp [Matrix.mul_sub, hPi2, hPiR]
  have hER : E * R = 0 := by rw [hE]; simp [Matrix.sub_mul, hR2, hPiR]
  have hEE : E * E = E := by
    nth_rewrite 2 [hE]
    rw [Matrix.mul_sub, Matrix.mul_sub, hEPi, hER, Matrix.mul_one, sub_zero, sub_zero]
  have hE1Pi : E * (1 - Pi) = E := by rw [Matrix.mul_sub, Matrix.mul_one, hEPi, sub_zero]
  have h1PiE : (1 - Pi) * E = E := by rw [Matrix.sub_mul, Matrix.one_mul, hPiE, sub_zero]
  have hR1Pi : R * (1 - Pi) = R := by rw [Matrix.mul_sub, Matrix.mul_one, hRPi, sub_zero]
  have h1PiR : (1 - Pi) * R = R := by rw [Matrix.sub_mul, Matrix.one_mul, hPiR, sub_zero]
  -- Step 1: `Re tr (S E) ≤ 0`
  have hSEle : RCLike.re (Matrix.trace (S * E)) ≤ 0 := by
    have hSE : Matrix.trace (E * S * E) = Matrix.trace (S * E) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hEE]
    have hKE' : ((1 - Pi) * P * (1 - Pi)) * E = 0 := by rw [hE]; exact hKE
    have hEPE : E * P * E = 0 := by
      calc E * P * E = (E * (1 - Pi)) * P * ((1 - Pi) * E) := by rw [hE1Pi, h1PiE]
        _ = E * (((1 - Pi) * P * (1 - Pi)) * E) := by noncomm_ring
        _ = 0 := by rw [hKE']; simp
    have hEQE : E * Q * E = Eᴴ * ((1 - Pi) * Q * (1 - Pi)) * E := by
      rw [hEh.eq]
      calc E * Q * E = (E * (1 - Pi)) * Q * ((1 - Pi) * E) := by rw [hE1Pi, h1PiE]
        _ = E * ((1 - Pi) * Q * (1 - Pi)) * E := by noncomm_ring
    have hsplit : E * S * E = E * P * E + E * Q * E := by rw [hS]; noncomm_ring
    rw [← hSE, hsplit, hEPE, hEQE, zero_add]
    exact re_trace_conj_nonpos hNSD
  -- Step 2: `Re tr (S R) ≤ Re tr P`
  have hSRle : RCLike.re (Matrix.trace (S * R)) ≤ RCLike.re P.trace := by
    have hRSR : Matrix.trace (R * S * R) = Matrix.trace (S * R) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hR2]
    have hsplit : R * S * R = R * P * R + R * Q * R := by rw [hS]; noncomm_ring
    have hRQR : RCLike.re (Matrix.trace (R * Q * R)) ≤ 0 := by
      have h : R * Q * R = Rᴴ * ((1 - Pi) * Q * (1 - Pi)) * R := by
        rw [hRh.eq]
        calc R * Q * R = (R * (1 - Pi)) * Q * ((1 - Pi) * R) := by rw [hR1Pi, h1PiR]
          _ = R * ((1 - Pi) * Q * (1 - Pi)) * R := by noncomm_ring
      rw [h]
      exact re_trace_conj_nonpos hNSD
    have h1R2 : (1 - R) * (1 - R) = 1 - R := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hR2]; simp
    have hRPR : RCLike.re (Matrix.trace (R * P * R)) ≤ RCLike.re P.trace := by
      have e1 : Matrix.trace ((1 - R) * P * (1 - R)) = Matrix.trace (P * (1 - R)) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h1R2]
      have e2 : Matrix.trace (R * P * R) = Matrix.trace (P * R) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hR2]
      have e3 : Matrix.trace (P * (1 - R)) = Matrix.trace P - Matrix.trace (P * R) := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
      have hpsd : ((1 - R)ᴴ * P * (1 - R)).PosSemidef := hP.conjTranspose_mul_mul_same _
      have hherm : (1 - R : Matrix n n 𝕜)ᴴ = 1 - R := by
        simp [Matrix.conjTranspose_sub, hRh.eq]
      rw [hherm] at hpsd
      have hnn := posSemidef_re_trace_nonneg hpsd
      rw [e1, e3] at hnn
      rw [e2]
      simp only [map_sub] at hnn
      linarith
    rw [← hRSR, hsplit, Matrix.trace_add, map_add]
    linarith
  -- Step 3: the Frobenius estimate against `M = c·Pi + (c/2)·R`
  obtain ⟨Mm, hM⟩ : ∃ Mm : Matrix n n 𝕜, Mm = c • Pi + (c / 2) • R := ⟨_, rfl⟩
  have hMh : Mm.IsHermitian := by
    rw [Matrix.IsHermitian, hM, Matrix.conjTranspose_add, conjTranspose_real_smul,
      conjTranspose_real_smul, hPih.eq, hRh.eq]
  have hMM : Mm * Mm = (c ^ 2) • Pi + (c ^ 2 / 4) • R := by
    rw [hM]
    simp only [Matrix.add_mul, Matrix.mul_add, smul_mul, Matrix.mul_smul, smul_smul, hPi2, hR2,
      hPiR, hRPi, smul_zero, add_zero, zero_add]
    congr 2 <;> ring
  have htrMM : RCLike.re (Matrix.trace (Mm * Mm))
      = c ^ 2 * RCLike.re Pi.trace + c ^ 2 / 4 * RCLike.re R.trace := by
    rw [hMM, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, map_add, RCLike.smul_re,
      RCLike.smul_re]
  have htrSM : RCLike.re (Matrix.trace (S * Mm))
      = c * RCLike.re (Matrix.trace (S * Pi)) + c / 2 * RCLike.re (Matrix.trace (S * R)) := by
    rw [hM, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, map_add, RCLike.smul_re, RCLike.smul_re]
  have hSPi : Matrix.trace (S * Pi)
      = Matrix.trace S - Matrix.trace (S * R) - Matrix.trace (S * E) := by
    have h1 : S * Pi = S - S * R - S * E := by rw [hE]; noncomm_ring
    rw [h1, Matrix.trace_sub, Matrix.trace_sub]
  have htrS : RCLike.re (Matrix.trace S) = RCLike.re P.trace + RCLike.re Q.trace := by
    rw [hS, Matrix.trace_add, map_add]
  have hkey := frobSq_nonneg (S - Mm)
  rw [frobSq_sub hSh hMh] at hkey
  have hfrobM : frobSq Mm = RCLike.re (Matrix.trace (Mm * Mm)) := by rw [frobSq, hMh.eq]
  have hb : c ^ 2 * RCLike.re Pi.trace ≤ c ^ 2 * b :=
    mul_le_mul_of_nonneg_left htPi (sq_nonneg c)
  have hr : c ^ 2 / 4 * RCLike.re R.trace ≤ c ^ 2 / 4 * r :=
    mul_le_mul_of_nonneg_left htR (by positivity)
  have hSRc : c * RCLike.re (Matrix.trace (S * R)) ≤ c * RCLike.re P.trace :=
    mul_le_mul_of_nonneg_left hSRle hc.le
  have hSEc : c * RCLike.re (Matrix.trace (S * E)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le hSEle
  rw [hfrobM, htrMM, htrSM, hSPi] at hkey
  simp only [map_sub] at hkey
  rw [htrS] at hkey
  have hFS : frobSq S = frobSq (P + Q) := by rw [hS]
  rw [hFS] at hkey
  linarith

/-! ## Main theorem -/

/-- **Rank–trace inequality**.  If `P` is positive semidefinite of rank at most `r`, `Q` is
Hermitian with at most `b` positive eigenvalues and `c > 0`, then
`c·Re tr P − (c²/4)·r + 2c·Re tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {P Q : Matrix n n 𝕜} {r b : ℕ} {c : ℝ}
    (hc : 0 < c) (hP : P.PosSemidef) (hPr : P.rank ≤ r)
    (hQ : Q.IsHermitian) (hQb : posIndex hQ ≤ b) :
    c * RCLike.re P.trace - c ^ 2 / 4 * r + 2 * c * RCLike.re Q.trace - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  classical
  -- `Pi` is the spectral projection of `Q` onto its positive eigenvalues
  obtain ⟨Pi, hPidef⟩ : ∃ X : Matrix n n 𝕜, X = specFun hQ (fun x => if 0 < x then 1 else 0) :=
    ⟨_, rfl⟩
  have hPih : Pi.IsHermitian := hPidef ▸ specFun_isHermitian hQ _
  have hPi2 : Pi * Pi = Pi := by
    rw [hPidef, specFun_mul]
    exact specFun_congr hQ (fun i => by by_cases h : 0 < hQ.eigenvalues i <;> simp [h])
  have htPi : RCLike.re Pi.trace ≤ (b : ℝ) := by
    rw [hPidef, re_trace_specFun_indicator]
    exact_mod_cast hQb
  have hcomp : (1 : Matrix n n 𝕜) - Pi = specFun hQ (fun x => if 0 < x then 0 else 1) := by
    have h : specFun hQ (fun x => (if 0 < x then (0 : ℝ) else 1) + (if 0 < x then 1 else 0))
        = specFun hQ (fun _ => 1) :=
      specFun_congr hQ (fun i => by by_cases h : 0 < hQ.eigenvalues i <;> simp [h])
    rw [sub_eq_iff_eq_add, hPidef, specFun_add, h, specFun_one]
  -- the compression of `Q` to the orthogonal complement is negative semidefinite
  have hNSD : (-((1 - Pi) * Q * (1 - Pi))).PosSemidef := by
    rw [hcomp]
    nth_rewrite 2 [← specFun_id hQ]
    rw [specFun_mul, specFun_mul, specFun_neg]
    refine specFun_posSemidef hQ _ (fun i => ?_)
    by_cases h : 0 < hQ.eigenvalues i
    · simp [h]
    · simp only [h, if_false, id, one_mul, mul_one, neg_nonneg]
      exact not_lt.mp h
  have hPicomp : Pi * (1 - Pi) = 0 := by
    rw [hcomp, hPidef, specFun_mul,
      specFun_congr hQ (f := fun x => (if 0 < x then (1 : ℝ) else 0) * (if 0 < x then 0 else 1))
        (g := fun _ => 0) (fun i => by by_cases h : 0 < hQ.eigenvalues i <;> simp [h]),
      specFun_zero]
  -- `R` is the projection onto the range of the compression of `P`
  have hcompH : ((1 : Matrix n n 𝕜) - Pi).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, hPih.eq]
  have hK : ((1 - Pi) * P * (1 - Pi)).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same ((1 : Matrix n n 𝕜) - Pi)
    rwa [hcompH.eq] at h
  obtain ⟨R, hRdef⟩ : ∃ X : Matrix n n 𝕜, X = specFun hK.1 (fun x => if x ≠ 0 then 1 else 0) :=
    ⟨_, rfl⟩
  have hRh : R.IsHermitian := hRdef ▸ specFun_isHermitian hK.1 _
  have hR2 : R * R = R := by
    rw [hRdef, specFun_mul]
    exact specFun_congr hK.1 (fun i => by by_cases h : hK.1.eigenvalues i ≠ 0 <;> simp [h])
  have htR : RCLike.re R.trace ≤ (r : ℝ) := by
    rw [hRdef, re_trace_specFun_indicator]
    have h1 : Fintype.card {i // hK.1.eigenvalues i ≠ 0} = ((1 - Pi) * P * (1 - Pi)).rank :=
      (Matrix.IsHermitian.rank_eq_card_non_zero_eigs hK.1).symm
    have h2 : ((1 - Pi) * P * (1 - Pi)).rank ≤ r :=
      le_trans (le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)) hPr
    rw [h1]
    exact_mod_cast h2
  have hKR : ((1 - Pi) * P * (1 - Pi)) * R = (1 - Pi) * P * (1 - Pi) := by
    have h1 : ((1 - Pi) * P * (1 - Pi)) * R
        = specFun hK.1 id * specFun hK.1 (fun x => if x ≠ 0 then 1 else 0) := by
      rw [hRdef, specFun_id]
    have h2 : ∀ i, id (hK.1.eigenvalues i) * (if hK.1.eigenvalues i ≠ 0 then (1 : ℝ) else 0)
        = id (hK.1.eigenvalues i) := by
      intro i
      by_cases h : hK.1.eigenvalues i ≠ 0
      · simp [h]
      · push_neg at h
        simp [h]
    rw [h1, specFun_mul, specFun_congr hK.1 h2, specFun_id]
  have hRK : R
      = ((1 - Pi) * P * (1 - Pi)) * specFun hK.1 (fun x => if x = 0 then 0 else 1 / x) := by
    have h1 : ((1 - Pi) * P * (1 - Pi)) * specFun hK.1 (fun x => if x = 0 then 0 else 1 / x)
        = specFun hK.1 id * specFun hK.1 (fun x => if x = 0 then 0 else 1 / x) := by
      rw [specFun_id]
    rw [h1, specFun_mul, hRdef]
    refine specFun_congr hK.1 (fun i => ?_)
    by_cases h : hK.1.eigenvalues i = 0 <;> simp [h] <;> field_simp
  have hPiK : Pi * ((1 - Pi) * P * (1 - Pi)) = 0 := by
    calc Pi * ((1 - Pi) * P * (1 - Pi)) = (Pi * (1 - Pi)) * P * (1 - Pi) := by noncomm_ring
      _ = 0 := by rw [hPicomp]; simp
  have hPiR : Pi * R = 0 := by rw [hRK, ← Matrix.mul_assoc, hPiK, Matrix.zero_mul]
  have hRPi : R * Pi = 0 := by
    have h := congrArg Matrix.conjTranspose hPiR
    rw [Matrix.conjTranspose_mul, hPih.eq, hRh.eq, Matrix.conjTranspose_zero] at h
    exact h
  have hKPi : ((1 - Pi) * P * (1 - Pi)) * Pi = 0 := by
    have h := congrArg Matrix.conjTranspose hPiK
    rw [Matrix.conjTranspose_mul, hPih.eq, hK.1.eq, Matrix.conjTranspose_zero] at h
    exact h
  have hKE : ((1 - Pi) * P * (1 - Pi)) * (1 - Pi - R) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, hKPi, hKR, sub_zero, sub_self]
  exact trace_ineq_of_projections hc hP hQ hPih hPi2 hRh hR2 hPiR hRPi htPi htR hNSD hKE

end Zeta23Core

