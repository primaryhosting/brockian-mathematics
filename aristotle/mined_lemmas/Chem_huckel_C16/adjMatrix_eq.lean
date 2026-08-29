/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem adjMatrix_eq : (SimpleGraph.cycleGraph 16).adjMatrix ℂ = U 1 + U 15 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  simp only [U, Matrix.add_apply, Matrix.of_apply, adj_iff]
  have hi := i.isLt
  by_cases h1 : (j : ℕ) = ((i : ℕ) + 1) % 16 <;> by_cases h2 : (j : ℕ) = ((i : ℕ) + 15) % 16 <;>
    simp [h1, h2] <;> omega

/-! ### The 16th roots of unity -/

/-- A primitive 16th root of unity. -/
