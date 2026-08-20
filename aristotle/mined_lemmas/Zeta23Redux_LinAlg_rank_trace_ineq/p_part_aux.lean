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

/-!
## Proof outline

Write `E` for the orthogonal projection onto the range of `P` (so `tr E = rank P`), `Π` for the
spectral projection of `Q` onto its positive eigenvalues (so `tr Π = posIndex Q`), `S = 1 - Π`
and `R = S E S`.  Testing the Hermitian matrix `A = P + Q` against the Hermitian matrix
`B = c Π + (c/2) R` via `0 ≤ ‖A - B‖_F²` gives `2 tr (A B) - ‖B‖_F² ≤ ‖A‖_F²`.  Since `Π R = 0`,
`‖B‖_F² = c² tr Π + (c²/4) tr (R²)`, and `tr (R²) ≤ tr E` because
`E S E - (E S E)² = ((1 - E) S E)ᴴ ((1 - E) S E)` is positive semidefinite.  The linear term
splits into a `P`-part, `2 tr (P Π) + tr (P R) ≥ tr P`, which is exactly
`0 ≤ tr ((1 - E S E) P (1 - E S E))`, and a `Q`-part, `2 tr (Q Π) + tr (Q R) ≥ 2 tr Q`, which is
checked eigenvalue by eigenvalue using `0 ≤ R ≤ 1` and `R Π = 0`.
-/

namespace Zeta23Redux.LinAlg

open Matrix Finset
open scoped ComplexOrder

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma p_part_aux {P E S : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hEh : E.IsHermitian)
    (hEE : E * E = E) (hEP : E * P = P) (hPE : P * E = P) (hS : S.IsHermitian) :
    0 ≤ rtrace P - 2 * rtrace (P * S) + rtrace (P * (S * E * S)) := by
  set G := E * S * E with hGdef
  have hGh : Gᴴ = G := by
    rw [hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hEh.eq, Matrix.mul_assoc]
  have hHh : ((1 : Matrix (Fin d) (Fin d) ℂ) - G)ᴴ = 1 - G := by
    rw [Matrix.conjTranspose_sub, hGh, Matrix.conjTranspose_one]
  have h0 : 0 ≤ rtrace ((1 - G)ᴴ * P * (1 - G)) :=
    rtrace_nonneg_of_posSemidef (hP.conjTranspose_mul_mul_same _)
  have hexp : (1 - G)ᴴ * P * (1 - G) = P - G * P - P * G + G * P * G := by
    rw [hHh]; noncomm_ring
  have eq2 : rtrace (P * G) = rtrace (P * S) := by
    have h : P * G = P * S * E := by
      rw [hGdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPE]
    rw [h, rtrace_comm, ← Matrix.mul_assoc, hEP]
  have eq1 : rtrace (G * P) = rtrace (P * S) := by
    have h : G * P = E * (S * P) := by
      rw [hGdef, Matrix.mul_assoc, hEP, Matrix.mul_assoc]
    rw [h, rtrace_comm, Matrix.mul_assoc, hPE, rtrace_comm]
  have eq3 : rtrace (G * P * G) = rtrace (P * (S * E * S)) := by
    have h1 : rtrace (G * P * G) = rtrace (P * (G * G)) := by
      rw [Matrix.mul_assoc, rtrace_comm, Matrix.mul_assoc]
    have h2 : G * G = E * S * E * S * E := by
      rw [hGdef, show (E * S * E) * (E * S * E) = E * S * (E * E) * S * E by noncomm_ring, hEE]
    have h3 : P * (E * S * E * S * E) = P * S * E * S * E := by
      rw [show P * (E * S * E * S * E) = (P * E) * (S * E * S * E) by noncomm_ring, hPE]
      noncomm_ring
    rw [h1, h2, h3, rtrace_comm,
      show E * (P * S * E * S) = (E * P) * (S * E * S) by noncomm_ring, hEP]
  rw [hexp] at h0
  simp only [rtrace_add, rtrace_sub] at h0
  rw [eq1, eq2, eq3] at h0
  linarith

/-- The estimate coming from the positive semidefinite part `P`. -/
