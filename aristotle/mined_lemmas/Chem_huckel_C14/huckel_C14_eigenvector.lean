import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


theorem huckel_C14_eigenvector (k : Fin 14) :
    (fun j : Fin 14 => zeta (j * k)) ≠ 0 ∧
      ((cycleGraph 14).adjMatrix ℂ).mulVec (fun j : Fin 14 => zeta (j * k))
        = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) : ℂ) • fun j : Fin 14 => zeta (j * k) := by
  constructor
  · intro h
    have h0 : zeta ((0 : Fin 14) * k) = 0 := congrFun h 0
    rw [zero_mul, zeta_zero] at h0
    exact one_ne_zero h0
  · funext j
    have hcol : ((cycleGraph 14).adjMatrix ℂ).mulVec (fun j : Fin 14 => zeta (j * k)) j
        = (A14 * P14) j k := by
      simp [Matrix.mulVec, Matrix.mul_apply, A14, P14, dotProduct]
    rw [hcol, A_mul_P, Matrix.mul_apply]
    have hR : ∑ l : Fin 14, P14 j l * Matrix.diagonal lam l k = P14 j k * lam k := by
      simp [Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']
    rw [hR, P14, lam, Pi.smul_apply, smul_eq_mul, mul_comm]

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

