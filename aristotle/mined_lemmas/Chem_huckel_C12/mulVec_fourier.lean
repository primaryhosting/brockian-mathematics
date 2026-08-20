/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
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

namespace Chem

open Finset Matrix

/-- `zeta a = exp (2πi a / 12)`, the `a`-th power of a primitive 12th root of unity. -/

lemma mulVec_fourier (k : Fin 12) :
    (SimpleGraph.cycleGraph 12).adjMatrix ℂ *ᵥ (fun j : Fin 12 => zeta ((k.val : ℤ) * j.val))
      = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) •
          (fun j : Fin 12 => zeta ((k.val : ℤ) * j.val)) := by
  funext i
  rw [adjMatrix_mulVec_cycle]
  have hsub : ∀ i : Fin 12, (((i - 1 : Fin 12).val : ℤ)) % 12 = ((i.val : ℤ) - 1) % 12 := by
    decide
  have hadd : ∀ i : Fin 12, (((i + 1 : Fin 12).val : ℤ)) % 12 = ((i.val : ℤ) + 1) % 12 := by
    decide
  have e1 : zeta ((k.val : ℤ) * ((i - 1 : Fin 12).val))
      = zeta ((k.val : ℤ) * i.val) * zeta (-(k.val : ℤ)) := by
    rw [← zeta_add]
    refine zeta_periodic ?_
    have := (Int.ModEq.mul_left (k.val : ℤ) (hsub i))
    simpa [Int.ModEq, mul_sub] using this
  have e2 : zeta ((k.val : ℤ) * ((i + 1 : Fin 12).val))
      = zeta ((k.val : ℤ) * i.val) * zeta ((k.val : ℤ)) := by
    rw [← zeta_add]
    refine zeta_periodic ?_
    have := (Int.ModEq.mul_left (k.val : ℤ) (hadd i))
    simpa [Int.ModEq, mul_add] using this
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, two_cos_eq k.val]
  ring

/-- Every eigenvalue of the adjacency matrix of `C₁₂` is one of the `2 cos (2πk/12)`. -/
