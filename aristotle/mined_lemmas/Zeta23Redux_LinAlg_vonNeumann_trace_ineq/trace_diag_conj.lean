import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

lemma trace_diag_conj (a b : Fin d → ℝ) (W : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) * W * Matrix.diagonal (fun j => (b j : ℂ)) * star W).trace
      = ((∑ i, ∑ j, a i * b j * ‖W i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ← mul_star_eq_normSq]
  ring

/-- **Von Neumann's trace inequality** for Hermitian complex matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in the same (decreasing) order, then
`Re (tr (A * B)) ≤ ∑ i, mu i * nu i`.

The proof diagonalises both matrices, reduces the trace to a bilinear form against the entrywise
squared modulus of a unitary matrix — which is doubly stochastic — and then concludes by
Birkhoff's theorem together with the rearrangement inequality. -/
