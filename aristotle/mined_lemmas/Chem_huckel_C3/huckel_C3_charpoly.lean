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

namespace Chem

open Polynomial

/-- The adjacency matrix (Hückel matrix, in units where α = 0 and β = 1) of the cycle
graph `C₃`, over the reals. -/

theorem huckel_C3_charpoly :
    C3adj.charpoly = ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) := by
  rw [Fin.prod_univ_three, two_cos_C3 0, two_cos_C3 1, two_cos_C3 2]
  rw [C3adj_eq, Matrix.charpoly, Matrix.charmatrix]
  simp [Matrix.det_fin_three, Polynomial.C_neg, Polynomial.C_ofNat]
  ring

end Chem

