import Mathlib

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

/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires every
-- `import` to precede any module docstring; the text is otherwise verbatim.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-! ## The binary field and the Hamming parity-check matrix -/

/-- The two-element field `GF(2)`. -/
abbrev F2 := ZMod 2

/-- Column `i` of the parity-check matrix of the `[7,4,3]` Hamming code: the binary
expansion of `i + 1`.  The seven columns are exactly the seven nonzero vectors of
`GF(2)³`, which is what makes the code single-error correcting. -/

theorem hcol_ne_zero (i : Fin 7) : hcol i ≠ 0 := by revert i; decide

/-! ## Pauli errors in the symplectic (binary) representation

A Pauli operator on 7 qubits is written, up to phase, as `X^x Z^z` with
`x, z : Fin 7 → GF(2)`.  Composition is addition of the vectors and commutation is
governed by the symplectic form below; this is the standard binary representation of
the Pauli group used in stabilizer theory. -/

/-- A Pauli operator on the seven qubits, up to phase, in binary symplectic form. -/
structure Pauli where
  /-- The `X`-part of the Pauli operator. -/
  x : Fin 7 → F2
  /-- The `Z`-part of the Pauli operator. -/
  z : Fin 7 → F2

/-- Decidable equality of Paulis, defined component-wise so that it reduces well in the
kernel (the auto-derived instance gets stuck on `Eq.rec`). -/
instance : DecidableEq Pauli := fun P Q =>
  decidable_of_iff (P.x = Q.x ∧ P.z = Q.z) (by cases P; cases Q; simp)

instance : Fintype Pauli :=
  Fintype.ofEquiv ((Fin 7 → F2) × (Fin 7 → F2))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun P => (P.x, P.z)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The symplectic form on Pauli operators: `sympl P Q = 0` exactly when `P` and `Q`
commute, and `sympl P Q = 1` exactly when they anticommute. -/
