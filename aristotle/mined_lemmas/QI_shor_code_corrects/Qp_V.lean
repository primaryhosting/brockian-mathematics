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

lemma Qp_V (n : J × Bool) : Qp (V n) = V n := by
  rw [Qp_apply]
  simp only [V_orthonormal, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ n V, if_pos (Finset.mem_univ n)]

/-- Kraus operators of the recovery channel: one for each correctable error class,
plus a "no correction possible" operator, which annihilates every corrupted code state. -/
