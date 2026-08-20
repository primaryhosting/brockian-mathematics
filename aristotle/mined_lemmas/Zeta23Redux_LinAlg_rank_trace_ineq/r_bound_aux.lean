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

lemma r_bound_aux {E T : Matrix (Fin d) (Fin d) ℂ} (hEh : E.IsHermitian) (hEE : E * E = E)
    (hTh : T.IsHermitian) (hTT : T * T = T) :
    rtrace (((1 - T) * E * (1 - T)) * ((1 - T) * E * (1 - T))) ≤ rtrace E := by
  set S : Matrix (Fin d) (Fin d) ℂ := 1 - T with hSdef
  have hSh : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_sub, hTh.eq, Matrix.conjTranspose_one]
  have hSS : S * S = S := by
    rw [hSdef,
      show ((1 : Matrix (Fin d) (Fin d) ℂ) - T) * (1 - T) = 1 - T - T + T * T by noncomm_ring, hTT]
    abel
  set G := E * S * E with hGdef
  have hRR : rtrace ((S * E * S) * (S * E * S)) = rtrace (E * S * E * S) := by
    rw [show (S * E * S) * (S * E * S) = S * (E * (S * S) * E * S) by noncomm_ring, hSS,
      rtrace_comm, show (E * S * E * S) * S = E * S * E * (S * S) by noncomm_ring, hSS]
  have e2 : G * G = E * S * E * S * E := by
    rw [hGdef, show (E * S * E) * (E * S * E) = E * S * (E * E) * S * E by noncomm_ring, hEE]
  have hGG : rtrace (G * G) = rtrace (E * S * E * S) := by
    rw [e2, rtrace_comm, show E * (E * S * E * S) = (E * E) * S * E * S by noncomm_ring, hEE]
  have hZ : G - G * G = ((1 - E) * S * E)ᴴ * ((1 - E) * S * E) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hEh.eq, hSh,
      Matrix.conjTranspose_sub, hEh.eq, Matrix.conjTranspose_one, e2, hGdef,
      show E * (S * (1 - E)) * ((1 - E) * S * E)
        = E * (S * S) * E - E * S * E * S * E - E * S * E * S * E + E * S * ((E * E) * S * E)
        by noncomm_ring, hSS, hEE]
    noncomm_ring
  have h1 : rtrace (G * G) ≤ rtrace G := by
    have h := rtrace_nonneg_of_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self ((1 - E) * S * E))
    rw [← hZ, rtrace_sub] at h
    linarith
  have h2 : rtrace G ≤ rtrace E := by
    have hET : 0 ≤ rtrace (E * T) := by
      have h := rtrace_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self (T * E))
      rw [Matrix.conjTranspose_mul, hEh.eq, hTh.eq] at h
      rw [show (E * T) * (T * E) = E * (T * T) * E by noncomm_ring, hTT, rtrace_comm,
        show E * (E * T) = (E * E) * T by noncomm_ring, hEE] at h
      exact h
    have hg : rtrace G = rtrace E - rtrace (E * T) := by
      rw [hGdef, rtrace_comm, show E * (E * S) = (E * E) * S by noncomm_ring, hEE, hSdef,
        Matrix.mul_sub, Matrix.mul_one, rtrace_sub]
    linarith
  rw [hRR, ← hGG]
  linarith

/-- The Frobenius norm bound on the "test matrix" piece built from the support projection. -/
