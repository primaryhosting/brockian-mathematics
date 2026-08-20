/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

lemma cx_mul_right {n : ℕ} {i j : Fin n} (h : i ≠ j) (M : Matrix (Bits n) (Bits n) ℂ)
    (y x : Bits n) : (M * gateMat (Gate.CX i j h)) y x = M y (cxMap i j x) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (cxMap i j x)]
  · simp [gateMat]
  · intro z _ hz
    simp only [gateMat, Matrix.of_apply]
    rw [if_neg (fun hcon => hz hcon), mul_zero]
  · intro hc; exact absurd (Finset.mem_univ _) hc

