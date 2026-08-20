/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/

theorem steane_syndrome_X (v w : Bits) (psi : State) (hpsi : IsCode psi) (k : Fin 3) :
    Xop (Hrow k) (Err v w psi) = sgn (syn w k) • Err v w psi := by
  have h1 : Xop (Hrow k) (Zop w psi) = sgn (syn w k) • Zop w psi := by
    rw [Xop_Zop_comm, (hpsi k).1, dot_comm]; rfl
  calc Xop (Hrow k) (Err v w psi) = Xop v (Xop (Hrow k) (Zop w psi)) := by
        simp only [Err, Xop_Xop, add_comm]
    _ = sgn (syn w k) • Err v w psi := by rw [h1, Xop_smul]; rfl

/-! ## The decoder is correct on weight ≤ 1 errors -/

