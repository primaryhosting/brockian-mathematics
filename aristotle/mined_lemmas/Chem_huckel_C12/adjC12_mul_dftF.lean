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

lemma adjC12_mul_dftF : adjC12 * dftF = dftF * eigD := by
  have hadd : ∀ j : Fin 12, ((j + 1 : Fin 12) : ℕ) = (j.val + 1) % 12 := by decide
  have hsub : ∀ j : Fin 12, ((j - 1 : Fin 12) : ℕ) = (j.val + 11) % 12 := by decide
  ext j k
  rw [Matrix.mul_apply, adjC12_mulVec_apply (fun i => dftF i k) j, eigD, Matrix.mul_diagonal]
  show w ^ (((j + 1 : Fin 12) : ℕ) * k.val) + w ^ (((j - 1 : Fin 12) : ℕ) * k.val)
      = w ^ (j.val * k.val) * ((huckelEigenvalue k : ℝ) : ℂ)
  have e1 : w ^ (((j + 1 : Fin 12) : ℕ) * k.val) = w ^ (j.val * k.val + k.val) := by
    refine w_pow_congr ?_
    rw [hadd]
    simp [add_mul]
  have e2 : w ^ (((j - 1 : Fin 12) : ℕ) * k.val) = w ^ (j.val * k.val + 11 * k.val) := by
    refine w_pow_congr ?_
    rw [hsub]
    simp [add_mul]
  rw [e1, e2, pow_add, pow_add, huckelEigenvalue, ← w_pow_add_w_pow k.val]
  ring

/-- The characteristic polynomial of the adjacency matrix of `C₁₂`. -/
