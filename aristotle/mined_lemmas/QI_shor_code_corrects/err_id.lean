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

lemma err_id (i : Qb) (psi : H) : err i (fun x y => if x = y then 1 else 0) psi = psi := by
  funext v
  have hset : setq v i (v i) = v := by
    funext q; simp only [setq]; split <;> simp_all
  show ∑ b : Bool, (if v i = b then (1:ℂ) else 0) * psi (setq v i b) = psi v
  rw [Finset.sum_eq_single (v i) (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp [hset]

/-! ## The correctable error basis -/

/-- Index set for a maximal set of inequivalent single-qubit Pauli errors:
identity, `X i` and `X i Z i` for each qubit `i`, and one `Z` per block. -/
abbrev J := (Option (Qb × Bool)) ⊕ (Fin 3)

/-- `X`-part of the `j`-th error. -/
