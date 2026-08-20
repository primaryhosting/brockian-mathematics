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

lemma not_blkish_xr {v u : Cfg} (hv : blkish v) (hu : ¬ blkish u) : ¬ blkish (xr v u) := by
  intro h
  apply hu
  intro b k k'
  have h1 : xor (v (b,k)) (u (b,k)) = xor (v (b,k')) (u (b,k')) := h b k k'
  have h2 : v (b,k) = v (b,k') := hv b k k'
  revert h1 h2
  cases v (b,k) <;> cases v (b,k') <;> cases u (b,k) <;> cases u (b,k') <;> simp

