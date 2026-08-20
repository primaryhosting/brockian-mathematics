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

theorem huckel_C20_eigenvector (k : Fin 20) :
    (fun j : Fin 20 => ec (j * k)) ≠ 0 ∧
      ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) *ᵥ (fun j : Fin 20 => ec (j * k))
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) •
            (fun j : Fin 20 => ec (j * k)) := by
  constructor
  · intro h
    have h0 : ec ((0 : Fin 20) * k) = 0 := congrFun h 0
    rw [zero_mul, ec_zero] at h0
    exact one_ne_zero h0
  · funext j
    rw [Matrix.mulVec, dotProduct, adj_row_sum (fun m => ec (m * k)) j]
    simpa using ec_neighbour_sum j k

end Chem

