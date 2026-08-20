import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem huckel_C9_eigenvector (k : Fin 9) :
    ((SimpleGraph.cycleGraph 9).adjMatrix ℂ).mulVec
        (fun j : Fin 9 => Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9)) =
      ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ) •
        (fun j : Fin 9 => Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9)) := by
  have hcol : ∀ j : Fin 9,
      Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / 9) = Vm j k := by
    intro j
    rw [Vm, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  funext j
  have h := congrFun (congrFun adj_mul_Vm j) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hcol]
  rw [h]
  simp only [lam]
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

