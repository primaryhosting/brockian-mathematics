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

theorem ip_qop_diag (q₁ q₂ : Qb) (M₁ M₂ : Bool → Bool → ℂ) (κ : Bool) :
    ip (qop q₁ M₁ (cw κ)) (qop q₂ M₂ (cw κ))
      = ip (qop q₁ M₁ (cw false)) (qop q₂ M₂ (cw false)) := by
  have key : ∀ (s : Sg) (A B : ℂ), (starRingEnd ℂ) (nrm * sg κ s * A) * (nrm * sg κ s * B)
      = (starRingEnd ℂ) (nrm * sg false s * A) * (nrm * sg false s * B) := by
    intro s A B
    have h1 := sg_mul_self κ s
    calc (starRingEnd ℂ) (nrm * sg κ s * A) * (nrm * sg κ s * B)
        = (sg κ s * sg κ s) * ((starRingEnd ℂ) nrm * (starRingEnd ℂ) A * (nrm * B)) := by
          simp only [map_mul, conj_sg]; ring
      _ = (starRingEnd ℂ) nrm * (starRingEnd ℂ) A * (nrm * B) := by rw [h1, one_mul]
      _ = (starRingEnd ℂ) (nrm * sg false s * A) * (nrm * sg false s * B) := by
          simp only [sg, map_mul, map_one, if_neg (Bool.false_ne_true)]; ring
  by_cases hq : q₁ = q₂
  · subst hq
    rw [ip_qop_same, ip_qop_same]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => key s _ _
  · rw [ip_qop_diff q₁ q₂ hq, ip_qop_diff q₁ q₂ hq]
    exact Finset.sum_congr rfl fun s _ => key s _ _

/-- The off-diagonal Knill–Laflamme matrix elements vanish. -/
