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

The Hückel π-electron energy levels of benzene-like annulenes come from the adjacency
spectrum of a cycle graph.  Here we compute the spectrum of the cycle `C₁₂`: the
eigenvalues of its adjacency matrix are exactly `2 cos (2πk/12)` for `k = 0, …, 11`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier
transform: with `ζ = exp (2πi/12)` and `P i k = ζ^(i k)` (a Vandermonde matrix in the
powers of `ζ`) one has `A P = P D` with `D` diagonal with entries `2 cos (2πk/12)`,
and `P` is invertible since `ζ` is a primitive 12-th root of unity.

Main Mathlib inputs: `Complex.isPrimitiveRoot_exp`, `Matrix.det_vandermonde_eq_zero_iff`,
`Matrix.charpoly_units_conj`, `Matrix.charpoly_diagonal`,
`Matrix.mem_spectrum_iff_isRoot_charpoly`.
-/

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- A primitive 12-th root of unity. -/

theorem P12_isUnit : IsUnit P12 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, P12_eq_vandermonde,
    Ne, Matrix.det_vandermonde_eq_zero_iff]
  push_neg
  intro i j h
  exact Fin.ext (isPrimitiveRoot_zeta12.pow_inj i.isLt j.isLt h)

/-- The characteristic polynomial of the adjacency matrix of `C₁₂` splits with roots the
Hückel levels `2 cos (2πk/12)`, `k = 0, …, 11` (with multiplicity). -/
