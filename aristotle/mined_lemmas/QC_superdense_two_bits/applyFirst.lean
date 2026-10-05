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

set_option grind.warning false

namespace QC

/-- A two-qubit pure state is a vector of amplitudes indexed by the computational
basis `|ij⟩`, `i j : Fin 2`. -/
abbrev TwoQubit : Type := Fin 2 × Fin 2 → ℂ

/-- The Bell state `Φ⁺ = (|00⟩ + |11⟩)/√2`, shared by Alice (first qubit) and Bob
(second qubit) before the protocol starts. -/

noncomputable def applyFirst (M : Matrix (Fin 2) (Fin 2) ℂ) (v : TwoQubit) : TwoQubit :=
  fun p => ∑ k : Fin 2, M p.1 k * v (k, p.2)

/-- The Pauli `X` (bit flip) gate. -/
