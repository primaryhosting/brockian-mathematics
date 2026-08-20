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

def Qp : H →ₗ[ℂ] H where
  toFun φ := ∑ m : J × Bool, ip (V m) φ • V m
  map_add' := by
    intro x y
    simp only [ip_add_right, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [ip_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]

