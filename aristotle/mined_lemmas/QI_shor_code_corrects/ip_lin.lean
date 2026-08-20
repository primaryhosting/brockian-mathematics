import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with the state space of nine qubits, realized concretely as the space of
complex-valued functions on the set `Bs` of computational basis states, where a basis
state is an assignment of a bit to each of the nine qubits.  Qubits are indexed by
`Qb = Fin 3 × Fin 3`: the first component is the index of one of the three blocks of the
Shor code, the second is the position inside that block.

An *arbitrary single-qubit error* acting on qubit `q` is the operator `qop q M` attached to
an arbitrary `2 × 2` complex matrix `M : Bool → Bool → ℂ` acting on qubit `q` and acting as
the identity on all other qubits.  Every completely arbitrary (not necessarily unitary)
one-qubit operation is of this form.

The Shor codewords are

  `cw false = (1/(2√2)) (|000⟩+|111⟩) ⊗ (|000⟩+|111⟩) ⊗ (|000⟩+|111⟩)`
  `cw true  = (1/(2√2)) (|000⟩-|111⟩) ⊗ (|000⟩-|111⟩) ⊗ (|000⟩-|111⟩)`

and the code space is their complex span.

The theorem `QI.shor_code_corrects` states that

* the two codewords are orthonormal, so the code space is a genuine two-dimensional
  (one logical qubit) subspace; and
* for **any** pair of single-qubit errors `E = qop q₁ M₁` and `F = qop q₂ M₂` there is a
  scalar `c` with `⟪E x, F y⟫ = c ⟪x, y⟫` for all code vectors `x, y`.

The second item is exactly the Knill–Laflamme error-correction condition
`P E† F P = c_{EF} P` for the set of all single-qubit errors, i.e. the statement that the
Shor code corrects an arbitrary single-qubit error.
-/

namespace QI

open Finset

/-- Qubit labels: `(block, position in block)`. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits. -/
abbrev Bs := Qb → Bool

/-- Labels for the eight basis states that occur in the Shor codewords: a bit per block. -/
abbrev Sg := Fin 3 → Bool

/-- The basis state in which all three qubits of block `i` carry the bit `s i`. -/

lemma ip_lin (α β γ δ : ℂ) (x y u v : Bs → ℂ) :
    ip (fun b => α * x b + β * y b) (fun b => γ * u b + δ * v b)
      = (starRingEnd ℂ) α * γ * ip x u + (starRingEnd ℂ) α * δ * ip x v
        + (starRingEnd ℂ) β * γ * ip y u + (starRingEnd ℂ) β * δ * ip y v := by
  simp only [ip, map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-! ### Main theorem -/

/-- The codewords lie in the code space, so the statement below is not vacuous. -/
