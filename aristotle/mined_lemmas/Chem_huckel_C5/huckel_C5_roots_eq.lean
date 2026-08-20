import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl,
with `α = 0`, `β = 1`): vertices `0,1,2,3,4` in a cycle, `A i j = 1` iff `i` and `j`
are adjacent along the cycle. -/

theorem huckel_C5_roots_eq :
    C5adj.charpoly.roots = (Finset.univ : Finset (Fin 5)).val.map
      (fun k => 2 * Real.cos (2 * π * (k : ℕ) / 5)) := by
  have h : (∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 5))) : ℝ[X])
      = (((Finset.univ : Finset (Fin 5)).val.map
            (fun k => 2 * Real.cos (2 * π * (k : ℕ) / 5))).map (fun a => X - C a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [huckel_C5, h, Polynomial.roots_multiset_prod_X_sub_C]

/-- Consequence: for each `k`, the number `2·cos(2πk/5)` really is an eigenvalue of the
adjacency matrix of `C₅`, i.e. it admits a nonzero eigenvector. -/
