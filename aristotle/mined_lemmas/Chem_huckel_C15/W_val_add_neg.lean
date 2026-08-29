/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma W_val_add_neg (k : Fin 15) :
    W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ)) = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 15 with ht
  have hW : W ((k : ℕ) : ℤ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [W, zpow_natCast, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hWneg : W (-((k : ℕ) : ℤ)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [W_neg, hW, ← Complex.exp_neg]
  rw [hW, hWneg, Complex.exp_mul_I]
  have hneg : Complex.exp (-((t : ℂ) * Complex.I)) = Complex.cos t - Complex.sin t * Complex.I := by
    rw [show -((t : ℂ) * Complex.I) = (-(t : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hneg, Complex.ofReal_cos]
  ring

/-- The action of the adjacency matrix of `C₁₅`. -/
