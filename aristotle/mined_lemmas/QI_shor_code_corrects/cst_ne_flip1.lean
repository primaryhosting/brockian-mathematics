/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring to precede the `import` line; the text is otherwise verbatim.)

import Mathlib

/-!
## Overview

We work with the state space of nine qubits, `ℂ^(2^9)`, realized concretely as the space
`St = (Fin 9 → Bool) → ℂ` of complex-valued functions on the computational basis labels
`Qbits = Fin 9 → Bool`, with the standard Hermitian inner product `ip`.

The nine-qubit Shor code is the two-dimensional subspace spanned by the orthonormal logical
states

  `|0_L⟩ = 2^(-3/2) (|000⟩+|111⟩)(|000⟩+|111⟩)(|000⟩+|111⟩)`,
  `|1_L⟩ = 2^(-3/2) (|000⟩-|111⟩)(|000⟩-|111⟩)(|000⟩-|111⟩)`.

An *arbitrary single-qubit error* on qubit `k` is an arbitrary linear operator acting on the
`k`-th tensor factor and as the identity elsewhere; it is described by an arbitrary `2 × 2`
complex matrix `M : Bool → Bool → ℂ` through the operator `qubitOp k M`.

The final theorem `QI.shor_code_corrects` states:

* the logical states are orthonormal (so the code is a genuine two-dimensional code), and
* the Knill–Laflamme error-correction conditions hold for the set of all single-qubit errors:
  for all qubits `k, l` and all single-qubit operators `M, N`,
  `⟨i_L| (qubitOp k M)† (qubitOp l N) |j_L⟩ = γ δ_{ij}`
  for a scalar `γ` depending only on the errors and not on the logical state.

The Knill–Laflamme conditions are the standard necessary and sufficient criterion for the
existence of a recovery channel correcting the given error set; since the set of single-qubit
errors is closed under the operations involved, this says precisely that the Shor code corrects
an arbitrary single-qubit error.
-/

namespace QI

open Finset

/-- Computational basis labels for nine qubits. -/
abbrev Qbits : Type := Fin 9 → Bool

/-- The state space of nine qubits, `ℂ^(2^9)`, as functions on basis labels. -/
abbrev St : Type := Qbits → ℂ

/-- The standard Hermitian inner product, conjugate linear in the first variable. -/

lemma cst_ne_flip1 (k : Fin 9) (s t : Bool × Bool × Bool) : flipAt k (cst s) ≠ cst t := by
  obtain ⟨m, hm, hmk, -⟩ := exists_partner k k
  intro h
  have h1 := congrFun h k
  have h2 := congrFun h m
  simp [flipAt, hmk] at h1 h2
  rw [cst_block (s := t) hm, cst_block (s := s) hm] at h2
  rw [← h2] at h1
  exact (Bool.not_ne_self _) h1.symm

