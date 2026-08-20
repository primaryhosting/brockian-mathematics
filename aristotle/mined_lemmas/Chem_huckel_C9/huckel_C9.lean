/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for `C₉`

The Hückel matrix of the cycle `C₉` (in units where the Coulomb integral is `0` and the
resonance integral is `1`) is the adjacency matrix of `SimpleGraph.cycleGraph 9`.
This file diagonalizes it by the discrete Fourier transform (a Vandermonde matrix built from
a primitive ninth root of unity) and computes its characteristic polynomial and spectrum:
the eigenvalues are `2 cos (2πk/9)`, `k = 0, …, 8`.
-/

open Matrix Polynomial SimpleGraph

namespace Chem

/-- A primitive ninth root of unity. -/

theorem huckel_C9 :
    spectrum ℂ ((cycleGraph 9).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 9, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 9)} := by
  ext μ
  rw [Set.mem_setOf_eq, show (cycleGraph 9).adjMatrix ℂ = A9 from rfl,
    Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C9_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero, lam]

end Chem

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

