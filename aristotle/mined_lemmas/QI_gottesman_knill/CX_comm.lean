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

lemma CX_comm {n : ℕ} {i j : Fin n} (h : i ≠ j) (P : Pauli n) :
    P.toMat * gateMat (Gate.CX i j h)
      = gateMat (Gate.CX i j h) * (stepPauli (Gate.CX i j h) P).toMat := by
  ext y x
  rw [cx_mul_right h, cx_mul_left h, stepPauli_CX]
  simp only [Pauli.toMat, Matrix.of_apply]
  rw [dotB_cxMap]
  by_cases hc : y = cxMap i j x + P.xs
  · have hc2 : cxMap i j y = x + cxMap i j P.xs := by
      rw [hc, cxMap_add, cxMap_involutive h]
    rw [if_pos hc, if_pos hc2]
  · have hc2 : ¬ (cxMap i j y = x + cxMap i j P.xs) := by
      intro hh
      apply hc
      have h3 := congrArg (cxMap i j) hh
      rwa [cxMap_involutive h, cxMap_add, cxMap_involutive h] at h3
    rw [if_neg hc, if_neg hc2]

