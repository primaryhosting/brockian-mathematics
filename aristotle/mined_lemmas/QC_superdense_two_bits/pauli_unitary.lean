import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Matrix

/-- The Pauli `X` (bit flip) matrix. -/

theorem pauli_unitary (a b : Bool) : (pauli a b)ᴴ * pauli a b = 1 := by
  cases a <;> cases b <;>
    simp [pauli, pauliX, pauliZ, Matrix.conjTranspose, Matrix.mul_fin_two,
      Matrix.one_fin_two, Matrix.ext_iff.symm, Fin.forall_fin_two] <;>
    norm_num [Matrix.one_fin_two, Matrix.ext_iff.symm, Fin.forall_fin_two]

/-- Explicit description of the encoded state: its `(i, j)` amplitude is the `(i, j)` entry of
the Pauli operator divided by `√2`. -/
