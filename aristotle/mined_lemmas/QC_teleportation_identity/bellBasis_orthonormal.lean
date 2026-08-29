import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

namespace QC

/-! ## Setup

A qubit state is a vector of amplitudes indexed by `Fin 2`.  Addition on `Fin 2`
is addition modulo `2`, i.e. the classical `xor` used to describe the Pauli `X`
gate and the Bell basis.
-/

/-- The amplitude `1/√2`, as a complex number. -/

lemma bellBasis_orthonormal (m n m' n' : Fin 2) :
    ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bellBasis m n i j) * bellBasis m' n' i j
      = if m = m' ∧ n = n' then 1 else 0 := by
  fin_cases m <;> fin_cases n <;> fin_cases m' <;> fin_cases n' <;>
    simp [bellBasis, Fin.sum_univ_two] <;> ring

/-! ## The teleportation identity -/

/-- **Teleportation identity.**  For every one–qubit input state `ψ` and every
Bell-measurement outcome `(m, n)`, applying Bob's correction `Z^m X^n` to his
conditional post-measurement state returns exactly the input state `ψ`. -/
