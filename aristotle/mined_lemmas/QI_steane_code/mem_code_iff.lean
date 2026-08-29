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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

We work with 7 qubits.  The computational basis of the state space is indexed by
`V2 = Fin 7 → ZMod 2` (bit strings of length 7), and a state is a function `Ket = V2 → ℂ`.

For `a b : V2` the Pauli operator `pauli a b` acts on basis kets by
`P(a,b) |v⟩ = (-1)^(b ⬝ v) |v + a⟩`; thus `pauli a 0` is a product of `X`'s on the support of
`a`, `pauli 0 b` a product of `Z`'s on the support of `b`, and `pauli a b` with `a = b`
supported on one qubit is `Y` on that qubit (up to the irrelevant global phase `i`).

The Steane code is the CSS code built from the `[7,4,3]` Hamming code: the two logical basis
states `u 0`, `u 1` are the uniform superpositions over the two cosets of the dual Hamming
code `C₂` (the `[7,3,4]` simplex code) inside the Hamming code.

The theorem `QI.steane_code` states the Knill–Laflamme error-correction conditions for the
set of *all* single-qubit Pauli errors, together with the fact that the two logical basis
states are orthogonal and nonzero (so the code space really is two-dimensional).
Since `⟪E u_i, F u_j⟫ = ⟪u_i, E† F u_j⟫`, the second conjunct is literally the
Knill–Laflamme condition `P E† F P = c_{E,F} · P` for the projector `P` onto the code space,
which is necessary and sufficient for the existence of a recovery channel correcting every
single-qubit error.
-/

/-- Bit strings of length 7 (indices of the computational basis of 7 qubits). -/
abbrev V2 := Fin 7 → ZMod 2

/-- A state of the 7 qubits, given by its computational-basis amplitudes. -/
abbrev Ket := V2 → ℂ

/-- The sign character `(-1) ^ x` of `ZMod 2`, valued in `ℂ`. -/

lemma mem_code_iff (v : V2) (j : Fin 2) : v ∈ code j ↔ v + shift j ∈ C2 := by
  simp only [code, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rwa [add_cancel_v2]
  · intro h
    exact ⟨v + shift j, h, add_cancel_v2 v (shift j)⟩

