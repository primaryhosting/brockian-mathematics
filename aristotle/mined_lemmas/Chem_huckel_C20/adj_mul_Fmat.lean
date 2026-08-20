/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma adj_mul_Fmat : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * Fmat = Fmat * Dmat := by
  ext j k
  rw [Matrix.mul_apply, adj_row_sum (fun m => Fmat m k) j]
  simp only [Fmat, Dmat, Matrix.of_apply, Matrix.mul_diagonal, Matrix.of_apply]
  rw [ec_neighbour_sum j k]
  ring

/-! ### Main theorem -/

/-- **Hückel theory for C₂₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` (the Hückel matrix of the annulene C₂₀H₂₀, with `α = 0`, `β = 1`)
factors as `∏ (X - 2cos(2πk/20))`, i.e. its adjacency eigenvalues, with multiplicity,
are exactly `2·cos(2πk/20)` for `k = 0, …, 19`. -/
