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

theorem steane_syndrome_Z (v w : Bits) (psi : State) (hpsi : IsCode psi) (k : Fin 3) :
    Zop (Hrow k) (Err v w psi) = sgn (syn v k) • Err v w psi := by
  have hz : Zop (Hrow k) (Zop w psi) = Zop w psi := by
    rw [Zop_Zop, add_comm, ← Zop_Zop, (hpsi k).2]
  have key := Xop_Zop_comm v (Hrow k) (Zop w psi)
  rw [hz] at key
  have h2 : Err v w psi = sgn (syn v k) • Zop (Hrow k) (Err v w psi) := key
  conv_rhs => rw [h2]
  rw [smul_smul, sgn_mul_self, one_smul]

/-- Measuring the `X`-type stabilizer `X_{H_k}` on an erroneous code state `E_{v,w} ψ`
returns the sign `(-1)^{(H w)_k}`, i.e. the `k`-th bit of the syndrome of the `Z`-part
of the error. -/
