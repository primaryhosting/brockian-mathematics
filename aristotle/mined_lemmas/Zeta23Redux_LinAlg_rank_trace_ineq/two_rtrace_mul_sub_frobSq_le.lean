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

lemma two_rtrace_mul_sub_frobSq_le {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : 2 * rtrace (A * B) - frobSq B ≤ frobSq A := by
  have h0 : 0 ≤ frobSq (A - B) := frobSq_nonneg _
  have hexp : frobSq (A - B) = frobSq A - 2 * rtrace (A * B) + frobSq B := by
    have h1 : (A - B)ᴴ = A - B := by
      rw [Matrix.conjTranspose_sub, hA.eq, hB.eq]
    have h2 : frobSq A = rtrace (A * A) := by
      rw [frobSq_eq_rtrace, hA.eq]
    have h3 : frobSq B = rtrace (B * B) := by
      rw [frobSq_eq_rtrace, hB.eq]
    rw [frobSq_eq_rtrace, h1, h2, h3, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      rtrace_sub, rtrace_sub, rtrace_sub, rtrace_comm B A]
    ring
  linarith

/-! ### Spectral functional calculus -/

/-- `sfc hA f` is `U * diagonal (f ∘ eigenvalues) * Uᴴ`, the functional calculus of the
Hermitian matrix `A` applied to `f`. -/
