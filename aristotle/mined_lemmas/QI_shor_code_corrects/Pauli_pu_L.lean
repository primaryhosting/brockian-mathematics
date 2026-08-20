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

lemma Pauli_pu_L (i : Qb) (p q : Bool) (a : Bool) :
    Pauli (pu i p) (pu i q) (L a) = V (corr i p q, a) := by
  cases p
  · cases q
    · rfl
    · -- degeneracy:  Z_{b,k} and Z_{b,0} agree on the code space
      simp only [pu, corr, V, uu, ww, if_true, if_false, Bool.false_eq_true]
      funext v
      rw [Pauli_apply, Pauli_apply, xr_zc, zph_uc, zph_uc]
      by_cases hv : blkish v
      · congr 2
        obtain ⟨b, k⟩ := i
        exact hv b k 0
      · rw [L_not_blkish hv]; ring
  · cases q <;> rfl

