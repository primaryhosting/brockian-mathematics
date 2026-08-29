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

theorem aeval_huckelPoly :
    aeval ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) huckelPoly = 0 := by
  have hA : (SimpleGraph.cycleGraph 16).adjMatrix ℂ = aeval (U 1) (X + X ^ 15 : ℂ[X]) := by
    rw [adjMatrix_eq]
    simp [U_one_pow]
  rw [hA, ← Polynomial.aeval_comp]
  obtain ⟨r, hr⟩ := dvd_huckelPoly_comp
  rw [hr, map_mul]
  have h16 : aeval (U 1) (X ^ 16 - 1 : ℂ[X]) = 0 := by
    simp [U_one_pow, U_sixteen]
  rw [h16, zero_mul]

/-! ### The two inclusions -/

