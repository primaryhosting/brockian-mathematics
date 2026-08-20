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

lemma err_L (i : Qb) (M : Bool → Bool → ℂ) (ψ : H) :
    err i M ψ = ∑ p : Bool, ∑ q : Bool, coef M p q • Pauli (pu i p) (pu i q) ψ := by
  funext v
  have hset0 : setq v i (v i) = v := by
    funext q; simp only [setq]; split <;> simp_all
  have hset1 : setq v i (!(v i)) = xr v (uc i) := by
    funext q
    simp only [setq, xr, uc]
    by_cases h : q = i
    · subst h; simp
    · simp [h]
  have hxr : (xr v (uc i)) i = !(v i) := by simp [xr]
  simp only [err, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_bool, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pauli_apply, pu, if_true, if_false,
    Bool.false_eq_true, xr_zc, zph_zc_left, zph_uc, one_mul]
  rw [hxr]
  cases h : v i
  · rw [h] at hset0
    simp only [h, Bool.not_false] at hset1 ⊢
    rw [hset0, hset1]
    simp only [coef, sg_false, sg_true]
    ring
  · rw [h] at hset0
    simp only [h, Bool.not_true] at hset1 ⊢
    rw [hset0, hset1]
    simp only [coef, sg_false, sg_true]
    ring

