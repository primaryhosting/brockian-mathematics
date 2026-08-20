import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem trace_mul_eq_trace_diag_conj {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) = Matrix.trace
      (diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
        * (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
            * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))
        * diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ))
        * star (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
            * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))) := by
  conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_mul, star_star, Function.comp_def,
    mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]
  rfl

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in the same (decreasing) order, then
`Re (tr (A * B)) ≤ ∑ i, mu i * nu i`. -/
