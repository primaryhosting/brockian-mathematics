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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the cyclic polyene `C₁₂H₁₂` uses the adjacency matrix of the cycle
graph `C₁₂`.  We show that the characteristic polynomial of this adjacency matrix is
`∏ k, (X - 2 cos (2πk/12))`, and consequently that the eigenvalues of the adjacency matrix
are exactly the numbers `2 cos (2πk/12)`, `k = 0, …, 11`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ω ^ (j * k)`, where `ω = exp (2πi/12)`.
-/

namespace Chem

open Complex Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₁₂`, viewed over `ℂ`. -/

lemma w_pow_add_w_pow (m : ℕ) :
    w ^ m + w ^ (11 * m) = ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ) := by
  have h1 : w ^ m * w ^ (11 * m) = 1 := by
    rw [← pow_add, show m + 11 * m = 12 * m by ring, pow_mul, w_pow_twelve, one_pow]
  have h2 : w ^ (11 * m) = (w ^ m)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  rw [h2, w_pow_eq_exp, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, ← neg_mul]
  ring

