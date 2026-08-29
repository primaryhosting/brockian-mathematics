/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

theorem huckel_C4_charpoly :
    C4Adj.charpoly = ∏ k : Fin 4, (Polynomial.X - Polynomial.C (cosEig k)) := by
  rw [Matrix.charpoly, charmatrix_C4Adj, det_cycle_four, Fin.prod_univ_four,
    cosEig_zero, cosEig_one, cosEig_two, cosEig_three]
  simp only [map_zero, map_neg, map_ofNat, sub_zero, sub_neg_eq_add]
  ring

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

