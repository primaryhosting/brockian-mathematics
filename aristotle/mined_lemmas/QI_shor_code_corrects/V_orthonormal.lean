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

lemma V_orthonormal (m n : J × Bool) : ip (V m) (V n) = if m = n then 1 else 0 := by
  obtain ⟨j, a⟩ := m
  obtain ⟨k, b⟩ := n
  simp only [V]
  rw [ip_Pauli_Pauli, ip_key a b _ _ (good_pairs j k)]
  by_cases hjk : j = k
  · subst hjk
    have h1 : (xr (uu j) (uu j) = zc ∧ (∀ β : Fin 3, mpar (xr (ww j) (ww j)) β = false)) :=
      (cond_pairs j j).2 rfl
    rw [if_pos h1, h1.1, zph_zc_right, one_mul]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Prod.ext_iff]
  · rw [if_neg (fun hc => hjk ((cond_pairs j k).1 hc))]
    simp [hjk, Prod.ext_iff]

/-! ## Expansion of a single-qubit error in the error basis -/

