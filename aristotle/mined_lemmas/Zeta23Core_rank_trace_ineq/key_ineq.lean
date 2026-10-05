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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/

lemma key_ineq {P Q Pi R Qm : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hPi : Pi.PosSemidef) (hPi2 : Pi * Pi = Pi)
    (hQm : Qm.PosSemidef) (hQPi : Q * Pi = Q + Qm)
    (hRH : R.IsHermitian) (hR2 : R * R = R)
    (hPR : P * R = P) (hPiR : Pi * R = Pi) (hRPi : R * Pi = Pi)
    {c : ℝ} (hc : 0 ≤ c) :
    c * rtr P + 2 * c * rtr Q - c ^ 2 / 4 * (rtr R + 3 * rtr Pi) ≤ frobSq (P + Q) := by
  set M : Matrix n n 𝕜 := P + Q with hM
  have hMH : M.IsHermitian := hP.isHermitian.add hQ
  set X : Matrix n n 𝕜 := (c / 2) • (R + Pi) with hXdef
  have hXH : X.IsHermitian := isHermitian_smul_real (hRH.add hPi.isHermitian) _
  have hXX : X * X = (c ^ 2 / 4) • (R + Pi + Pi + Pi) := by
    rw [hXdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, hR2, hPi2, hRPi, hPiR, show c / 2 * (c / 2) = c ^ 2 / 4 by ring]
    congr 1
    abel
  have hrXX : rtr (X * X) = c ^ 2 / 4 * (rtr R + 3 * rtr Pi) := by
    rw [hXX, rtr_smul, rtr_add, rtr_add, rtr_add]
    ring
  have hMR : M * R = P + Q * R := by rw [hM, Matrix.add_mul, hPR]
  have hQeq : Q = Q * Pi - Qm := by rw [hQPi]; abel
  have hQR : Q * R = Q + Qm - Qm * R := by
    conv_lhs => rw [hQeq]
    rw [Matrix.sub_mul, Matrix.mul_assoc, hPiR, hQPi]
  have hOneR : ((1 : Matrix n n 𝕜) - R).PosSemidef := by
    refine hermitian_idem_posSemidef (Matrix.isHermitian_one.sub hRH) ?_
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hR2]
    simp
  have hQmR : 0 ≤ rtr Qm - rtr (Qm * R) := by
    have h := rtr_mul_nonneg hQm hOneR
    rw [Matrix.mul_sub, Matrix.mul_one, rtr_sub] at h
    linarith
  have h1 : rtr P + rtr Q ≤ rtr (M * R) := by
    rw [hMR, rtr_add, hQR, rtr_sub, rtr_add]
    linarith
  have hMPi : M * Pi = P * Pi + (Q + Qm) := by rw [hM, Matrix.add_mul, hQPi]
  have h2 : rtr Q ≤ rtr (M * Pi) := by
    rw [hMPi, rtr_add, rtr_add]
    have ha := rtr_mul_nonneg hP hPi
    have hb := rtr_nonneg hQm
    linarith
  have hMX : rtr (M * X) = c / 2 * (rtr (M * R) + rtr (M * Pi)) := by
    rw [hXdef, Matrix.mul_smul, Matrix.mul_add, rtr_smul, rtr_add]
  have hkey := frobSq_lower hMH hXH
  rw [hrXX, hMX] at hkey
  have hmul : c * (rtr P + rtr Q + rtr Q) ≤ c * (rtr (M * R) + rtr (M * Pi)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  linarith [hkey, hmul]

/-! ### Main theorem -/

/-- **Rank–trace inequality** (Lemma 3.2).  If `P` is positive semidefinite with rank at most `r`,
`Q` is Hermitian with at most `b` positive eigenvalues, and `c > 0`, then
`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
