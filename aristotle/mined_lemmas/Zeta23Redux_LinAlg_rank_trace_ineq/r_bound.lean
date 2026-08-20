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

lemma r_bound {P T : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) (hT : T.IsHermitian)
    (hT2 : T * T = T) :
    rtrace (((1 - T) * suppProj hP.isHermitian * (1 - T)) *
      ((1 - T) * suppProj hP.isHermitian * (1 - T))) ≤ rtrace (suppProj hP.isHermitian) :=
  r_bound_aux (suppProj_isHermitian _) (suppProj_mul_self _) hT hT2

/-! ### The main theorem -/

/-- **The rank-trace inequality**. For `P` positive semidefinite with `rank P ≤ r`, and `Q`
Hermitian with at most `b` strictly positive eigenvalues, and every `c > 0`,
`c * rtrace P - (c²/4) * r + 2 * c * rtrace Q - c² * b ≤ frobSq (P + Q)`. -/
