/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment; it is repeated verbatim as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## The classical ingredients: the `[7,4,3]` Hamming code and its dual -/

/-- A binary register of 7 bits.  Also used to index the computational basis of the
7-qubit Hilbert space. -/
abbrev Reg := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form used both for parity checks and for Pauli phases. -/

lemma add_eq_zero_iff_reg (x y : Reg) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have : x + y + y = 0 + y := by rw [h]
    rwa [add_assoc, add_self_reg, add_zero, zero_add] at this
  · intro h; subst h; exact add_self_reg x

/-! ## Main theorem -/

/--
**The 7-qubit Steane code corrects any single-qubit error.**

The statement has three parts.

1. The two logical states `|0_L⟩`, `|1_L⟩` are orthogonal and nonzero, so the code
   space is genuinely two-dimensional (it encodes one qubit).

2. The Knill–Laflamme error-correction conditions hold for the set of all
   single-qubit errors: for any two Pauli operators `E₁ = X^{a₁}Z^{b₁}`,
   `E₂ = X^{a₂}Z^{b₂}` each supported on a single qubit, there is a constant `c`
   (independent of the logical state) with
   `⟨ψ_i| E₁† E₂ |ψ_j⟩ = c · δ_{ij}`.
   Since for each qubit `q` the four operators `X^a Z^b` with `a, b` supported in
   `{q}` span (up to phases) all operators on that qubit, this is exactly the
   necessary and sufficient condition for the existence of a recovery channel
   correcting an arbitrary error on one unknown qubit.

3. Operationally: the stabilizer syndrome separates single-qubit Pauli errors —
   two single-qubit Pauli errors with the same syndrome are equal, so syndrome
   measurement followed by the corresponding Pauli correction recovers the state.
-/
