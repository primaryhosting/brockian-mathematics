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

lemma key (p p' : Pauli) (k l : Fin 9) (i j : Bool) :
    ip (Pop p k (ulog i)) (Pop p' l (ulog j)) = if i = j then klCoeff p k p' l else 0 := by
  rw [Pop_selfadj, ip_ulog_left]
  cases p <;> cases p'
  -- (I, I)
  · simp only [Pop, ulog_cst]
    rw [sumS1]
    simp [klCoeff]
  -- (I, X)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (I, Y)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (I, Z)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.I k (Pop Pauli.Z l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx l) s) * co j s) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS2]
    simp [klCoeff]
  -- (X, I)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (X, X)
  · by_cases hkl : k = l
    · subst hkl
      simp only [Pop, flipAt_invol, ulog_cst]
      rw [sumS1]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (X, Y)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.X k (Pop Pauli.Y k (ulog j))) (cst s)
            = Complex.I * (co i s * (chi (sel (bidx k) s) * co j s)) := by
        intro s
        simp only [Pop, flipAt_self, flipAt_invol, ulog_cst, chi, cst_apply]
        cases sel (bidx k) s <;> simp <;> ring
      simp only [h]
      rw [← Finset.mul_sum, sumS2, mul_zero]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (X, Z)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Y, I)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Y, X)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.Y k (Pop Pauli.X k (ulog j))) (cst s)
            = (-Complex.I) * (co i s * (chi (sel (bidx k) s) * co j s)) := by
        intro s
        simp only [Pop, flipAt_invol, ulog_cst, chi, cst_apply]
        cases sel (bidx k) s <;> simp <;> ring
      simp only [h]
      rw [← Finset.mul_sum, sumS2, mul_zero]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (Y, Y)
  · by_cases hkl : k = l
    · subst hkl
      have h : ∀ s : Bool × Bool × Bool,
          co i s * (Pop Pauli.Y k (Pop Pauli.Y k (ulog j))) (cst s) = co i s * co j s := by
        intro s
        simp only [Pop, flipAt_self, flipAt_invol, ulog_cst]
        cases cst s k <;> simp <;> ring_nf <;> rw [Complex.I_sq] <;> ring
      simp only [h]
      rw [sumS1]
      simp [klCoeff]
    · simp [Pop, ulog_flip2 j (Ne.symm hkl), klCoeff, hkl]
  -- (Y, Z)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, I)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.Z k (Pop Pauli.I l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx k) s) * co j s) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS2]
    simp [klCoeff]
  -- (Z, X)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, Y)
  · simp [Pop, ulog_flip1, klCoeff]
  -- (Z, Z)
  · have h : ∀ s : Bool × Bool × Bool,
        co i s * (Pop Pauli.Z k (Pop Pauli.Z l (ulog j))) (cst s)
          = co i s * (chi (sel (bidx k) s) * (chi (sel (bidx l) s) * co j s)) := by
      intro s; simp [Pop, chi, cst_apply, ulog_cst]
    simp only [h]
    rw [sumS3]
    by_cases hij : i = j <;> by_cases hb : bidx k = bidx l <;> simp [klCoeff, hij, hb]

/-! ## Normalization of the logical states -/

