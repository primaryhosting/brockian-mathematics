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

lemma dftF_det_ne_zero : dftF.det ≠ 0 := by
  rw [dftF_eq_vandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  intro h
  have h2 : w ^ (j : ℕ) = w ^ (i : ℕ) := by linear_combination h
  have h3 := w_isPrimitiveRoot.pow_inj j.isLt i.isLt h2
  have h4 : (i : ℕ) < (j : ℕ) := hj
  omega

/-- Multiplying by the adjacency matrix of `C₁₂` sums the two neighbouring values. -/
