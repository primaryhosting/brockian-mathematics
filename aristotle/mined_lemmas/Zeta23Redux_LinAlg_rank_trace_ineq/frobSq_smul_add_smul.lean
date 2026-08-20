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

lemma frobSq_smul_add_smul {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (hXY : X * Y = 0) (hYX : Y * X = 0) (s t : ℝ) :
    frobSq (((s : ℂ)) • X + ((t : ℂ)) • Y) = s ^ 2 * frobSq X + t ^ 2 * frobSq Y := by
  have hh : (((s : ℂ)) • X + ((t : ℂ)) • Y)ᴴ = ((s : ℂ)) • X + ((t : ℂ)) • Y := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX.eq, hY.eq]
  have hprod : (((s : ℂ)) • X + ((t : ℂ)) • Y) * (((s : ℂ)) • X + ((t : ℂ)) • Y)
      = (((s ^ 2 : ℝ) : ℂ)) • (X * X) + (((t ^ 2 : ℝ) : ℂ)) • (Y * Y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hXY, hYX,
      smul_zero, add_zero, zero_add, smul_smul]
    push_cast
    rw [sq, sq]
  rw [frobSq_eq_rtrace, hh, hprod, rtrace_add, rtrace_smul, rtrace_smul, frobSq_eq_rtrace,
    frobSq_eq_rtrace, hX.eq, hY.eq]

