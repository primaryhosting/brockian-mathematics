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

lemma gateMat_S_diagonal {n : ℕ} (i : Fin n) :
    gateMat (Gate.S i) = Matrix.diagonal (fun x : Bits n => if x i = 0 then 1 else Complex.I) := by
  ext y x
  by_cases h : y = x
  · subst h
    rcases zmod2_cases (y i) with hb | hb <;>
      simp [gateMat, Zp, Pauli.toMat, iPowC_zero, dotB_unit_left, hb, sgnC] <;> ring
  · simp [gateMat, Zp, Pauli.toMat, h]

/-- The Hadamard gate acts as `2^(-1/2) (-1)^(y i * x i)` on qubit `i` and as the identity on the
other qubits. -/
