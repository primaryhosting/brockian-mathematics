/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma trace_conj_mul_conj (U V : Matrix n n ℂ) (a b : n → ℝ) :
    Matrix.trace ((U * Matrix.diagonal (fun i => (a i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun j => (b j : ℂ)) * star V))
      = Matrix.trace (star (star U * V) * Matrix.diagonal (fun i => (a i : ℂ)) * (star U * V) *
        Matrix.diagonal (fun j => (b j : ℂ))) := by
  set Da := Matrix.diagonal (fun i => (a i : ℂ))
  set Db := Matrix.diagonal (fun j => (b j : ℂ))
  have h1 : (U * Da * star U) * (V * Db * star V) = (U * Da * star U * V * Db) * star V := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.star_mul, star_star]
  simp [mul_assoc]

/--
**Von Neumann's trace inequality** for Hermitian complex matrices.

If `A` and `B` are Hermitian matrices of size `d`, and `mu`, `nu` are the eigenvalues of `A` and
`B` respectively (each an arbitrary rearrangement of the eigenvalue list), both listed in the same
monotone (decreasing) order, then `Re (tr (A * B)) ≤ ∑ i, mu i * nu i`.
-/
