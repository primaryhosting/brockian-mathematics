/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
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

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma C10adj_conj : C10adj = dftP * eigDiag * dftQ := by
  calc C10adj = C10adj * (dftP * dftQ) := by rw [dftP_mul_dftQ, Matrix.mul_one]
  _ = (C10adj * dftP) * dftQ := by rw [Matrix.mul_assoc]
  _ = dftP * eigDiag * dftQ := by rw [C10adj_mul_dftP]

/-- **Hückel theory for `C₁₀`.**  The characteristic polynomial of the adjacency matrix of
the cycle graph `C₁₀` is `∏_{k=0}^{9} (X - 2 cos (2πk/10))`, and consequently its spectrum
(the set of Hückel eigenvalues) is exactly `{2 cos (2πk/10) : k = 0, …, 9}`. -/
