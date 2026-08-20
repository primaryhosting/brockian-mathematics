import Mathlib
/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, and `/-! ... -/` is a module doc-comment *command*, not a comment token.  The
required header block is therefore placed immediately after the single `import Mathlib`
line, which is the closest legal position to the top of the file.
-/

namespace QI

open Finset

noncomputable section

/-! ## The 9-qubit state space -/

/-- Qubit labels: three blocks of three qubits. -/
abbrev Qb := Fin 3 × Fin 3

/-- Computational basis labels for 9 qubits. -/
abbrev Cfg := Qb → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)`. -/
abbrev H := Cfg → ℂ

/-- Hermitian inner product, conjugate linear in the first argument. -/

lemma zph_shift (w1 w2 t U : Cfg) :
    zph w1 t * zph w2 (xr t U) = zph w1 U * zph (xr w1 w2) (xr t U) := by
  rw [zph_xor_right, zph_xor_left, zph_xor_right, zph_xor_right]
  calc zph w1 t * (zph w2 t * zph w2 U)
      = 1 * (zph w1 t * (zph w2 t * zph w2 U)) := by ring
    _ = (zph w1 U * zph w1 U) * (zph w1 t * (zph w2 t * zph w2 U)) := by rw [zph_mul_self]
    _ = _ := by ring

/-- The Pauli operator `X^u Z^w`. -/
