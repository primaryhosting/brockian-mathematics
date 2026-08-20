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

lemma ip_key (a b : Bool) (u w : Cfg)
    (h : ¬ blkish u ∨ (u = zc ∧ ¬ (∀ β : Fin 3, mpar w β = true))) :
    ip (L a) (Pauli u w (L b))
      = if u = zc ∧ (∀ β : Fin 3, mpar w β = false) then (if a = b then 1 else 0) else 0 := by
  rcases h with hu | ⟨hu0, hnall⟩
  · have hne : ¬ (u = zc ∧ (∀ β : Fin 3, mpar w β = false)) := by
      rintro ⟨rfl, -⟩; exact hu blkish_zc
    rw [if_neg hne, ip_L]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Pauli_apply, L_not_blkish (not_blkish_xr (blk_blkish c) hu), mul_zero, mul_zero]
  · subst hu0
    rw [ip_L_Pauli_zc]
    simp only [true_and]
    by_cases hall : ∀ β : Fin 3, mpar w β = false
    · have hmu : ∀ β : Fin 3, mu w β = 1 := fun β => by rw [mu_eq, hall β]; rfl
      simp only [if_pos hall]
      by_cases hab : a = b
      · simp only [if_pos hab]
        have hp : ∀ β ∈ (Finset.univ : Finset (Fin 3)), (1 + (1:ℂ) * mu w β) = 2 := by
          intro β _; rw [hmu β]; norm_num
        rw [Finset.prod_congr rfl hp]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [nrm_sq]; norm_num
      · simp only [if_neg hab]
        rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) (by rw [hmu]; norm_num)]
        ring
    · simp only [if_neg hall]
      push_neg at hall
      obtain ⟨β0, hβ0⟩ := hall
      have hβ0' : mu w β0 = -1 := by
        have hb0 : mpar w β0 = true := by simpa using hβ0
        rw [mu_eq, hb0]; rfl
      by_cases hab : a = b
      · simp only [if_pos hab]
        rw [Finset.prod_eq_zero (Finset.mem_univ β0) (by rw [hβ0']; norm_num)]
        ring
      · simp only [if_neg hab]
        push_neg at hnall
        obtain ⟨β1, hβ1⟩ := hnall
        have hβ1' : mu w β1 = 1 := by
          have hb1 : mpar w β1 = false := by simpa using hβ1
          rw [mu_eq, hb1]; rfl
        rw [Finset.prod_eq_zero (Finset.mem_univ β1) (by rw [hβ1']; norm_num)]
        ring

/-! ## Single qubit errors -/

/-- Replace the value at qubit `i`. -/
