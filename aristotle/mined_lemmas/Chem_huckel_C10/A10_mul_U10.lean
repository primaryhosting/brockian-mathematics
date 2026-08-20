/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Polynomial Matrix Complex

/-- A primitive 10-th root of unity. -/

lemma A10_mul_U10 : A10 * U10 = U10 * D10 := by
  ext i k
  have hz10 : (w ^ (k : ℕ)) ^ (10 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, w_pow_ten, one_pow]
  have hinv : (w ^ (k : ℕ))⁻¹ = (w ^ (k : ℕ)) ^ 9 :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact hz10)
  have hcomm : ∀ j : ℕ, (w ^ j) ^ (k : ℕ) = (w ^ (k : ℕ)) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Matrix.mul_apply, D10, Matrix.mul_diagonal, ← w_pow_add_inv k, hinv, U10,
    Matrix.vandermonde_apply, hcomm]
  rw [← cycle_row (w ^ (k : ℕ)) hz10 i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [A10, SimpleGraph.adjMatrix_apply, Matrix.vandermonde_apply, hcomm]

