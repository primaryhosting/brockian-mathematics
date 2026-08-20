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
