/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
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

open Polynomial

/-- The Hückel matrix of the carbon skeleton of cyclobutadiene, in units where the Coulomb
integral `α` is `0` and the resonance integral `β` is `1`: the adjacency matrix of the cycle
graph `C₄`. -/

lemma C4adj_charpoly : C4adj.charpoly = (X - C 2) * X * (X + C 2) * X := by
  rw [C4adj_eq]
  have h1 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have h3 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  simp +decide [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    h1, h3, map_ofNat]
  ring

