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

theorem circuit_conj_pauli {n : ℕ} (C : List (Gate n)) (P : Pauli n) :
    (circuitMat C)ᴴ * P.toMat * circuitMat C = (simulate C P).toMat := by
  induction C with
  | nil => simp [circuitMat, simulate]
  | cons g gs ih =>
    simp only [circuitMat, simulate, Matrix.conjTranspose_mul]
    calc (gateMat g)ᴴ * (circuitMat gs)ᴴ * P.toMat * (circuitMat gs * gateMat g)
        = (gateMat g)ᴴ * ((circuitMat gs)ᴴ * P.toMat * circuitMat gs) * gateMat g := by
          simp [Matrix.mul_assoc]
      _ = (gateMat g)ᴴ * (simulate gs P).toMat * gateMat g := by rw [ih]
      _ = (stepPauli g (simulate gs P)).toMat := gate_conj_pauli _ _

