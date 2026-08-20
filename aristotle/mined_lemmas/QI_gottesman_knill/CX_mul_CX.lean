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

lemma CX_mul_CX {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    gateMat (Gate.CX i j h) * gateMat (Gate.CX i j h) = 1 := by
  ext y x
  rw [cx_mul_left h]
  simp only [gateMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hc : y = x
  · subst hc; simp
  · rw [if_neg, if_neg hc]
    intro hcon
    have h3 := congrArg (cxMap i j) hcon
    rw [cxMap_involutive h, cxMap_involutive h] at h3
    exact hc h3

/-! ### Unitarity and the Heisenberg picture for a general gate -/

