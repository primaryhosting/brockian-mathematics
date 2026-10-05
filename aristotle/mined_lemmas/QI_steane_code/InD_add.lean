import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the statement that the seven–qubit Steane CSS code corrects an
arbitrary error on a single qubit, in the standard Knill–Laflamme form:

for any two single–qubit Pauli errors `E₁`, `E₂` there is a constant `c`
(depending only on the errors) such that
`⟪E₁ ψ, E₂ φ⟫ = c * ⟪ψ, φ⟫` for all code states `ψ, φ`.

Everything is set up concretely.  The `2^7`-dimensional state space is modelled
as the space of functions `V → ℂ` where `V = Fin 7 → ZMod 2` indexes the
computational basis.  Pauli operators `X^a Z^b` act by
`(X^a Z^b) |v⟩ = (-1)^{b·v} |v + a⟩`, i.e. by `pauliOp`.  The Steane code space
is spanned by the two logical basis states
`|0_L⟩ = Σ_{v ∈ C} |v⟩` and `|1_L⟩ = Σ_{v ∈ C^⊥ \ C} |v⟩`,
where `C` is the `[7,3]` simplex code (the row span of the Hamming parity check
matrix `Hm`) and `C^⊥` is the `[7,4]` Hamming code.  Concretely a codeword `v`
lies in `C^⊥` iff all three parity checks vanish (`InD v`), and it lies in `C`
iff moreover it has even weight (`par v = 0`).
-/

namespace QI

/-- Bit strings of length seven: the index set of the computational basis. -/
abbrev V := Fin 7 → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

lemma InD_add {u v : V} (hu : InD u) (hv : InD v) : InD (u + v) := by
  intro k
  rw [dotp_add_right, hu k, hv k, add_zero]

