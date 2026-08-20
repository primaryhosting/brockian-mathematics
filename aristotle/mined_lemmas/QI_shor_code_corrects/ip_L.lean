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

lemma ip_L (a : Bool) (y : H) : ip (L a) y = ∑ c : Fin 3 → Bool, L a (blk c) * y (blk c) := by
  rw [ip]
  have h : ∀ v : Cfg, (starRingEnd ℂ) (L a v) * y v = if blkish v then L a v * y v else 0 := by
    intro v
    by_cases hv : blkish v
    · simp [hv, L_conj]
    · simp [hv, L_not_blkish hv]
  simp_rw [h]
  exact sum_blkish _

/-! ## Block parities -/

/-- Parity of the `Z`-support in block `b`. -/
