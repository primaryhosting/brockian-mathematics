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
