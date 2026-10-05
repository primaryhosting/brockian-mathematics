/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies `NC¹` (log-depth boolean formulas)
with width-`5` permutation branching programs:

* **Forward direction.** Every boolean formula of depth `d` is computed by a width-`5`
  permutation branching program of length at most `4 ^ d` (in the strong sense of
  `σ`-computation, for an arbitrary `5`-cycle `σ`).
* **Converse direction.** Every width-`5` permutation branching program of length at
  most `2 ^ k` is computed by a boolean formula of depth `O(k)` (explicitly `6 * k + 4`).

Together these say: depth-`d` formulas ↔ length-`4^d` width-`5` programs, i.e.
`NC¹` = width-`5` permutation branching programs.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### Boolean formulas -/

/-- Boolean formulas in `n` variables, over the complete basis `{¬, ∧}` together with
constants.  Depth-`O(log n)` formulas are exactly `NC¹`. -/
inductive Formula (n : ℕ) where
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  deriving DecidableEq

variable {n : ℕ}

/-- The boolean function computed by a formula. -/

theorem barrington_forward (i₀ : Fin n) (f : Formula n) :
    ∀ σ : Perm (Fin 5), IsFiveCycle σ →
      ∃ P : Program n, P.length ≤ 4 ^ f.depth ∧ P.Computes σ f.eval := by
  induction f with
  | const b =>
      intro σ _
      cases b with
      | false =>
          refine ⟨[], by simp, ?_⟩
          intro x; simp [Formula.eval]
      | true =>
          refine ⟨[(i₀, σ, σ)], by simp [Formula.depth], ?_⟩
          intro x; simp [Program.eval, Instr.eval, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[(i, σ, 1)], by simp [Formula.depth], ?_⟩
      intro x; simp [Program.eval, Instr.eval, Formula.eval]
  | not g ih =>
      intro σ hσ
      obtain ⟨P, hlen, hP⟩ := ih σ⁻¹ (isFiveCycle_inv hσ)
      refine ⟨P ++ [(i₀, σ, σ)], ?_, ?_⟩
      · have h1 : 1 ≤ (4 : ℕ) ^ g.depth := Nat.one_le_pow _ _ (by norm_num)
        simp only [Formula.depth, pow_succ, List.length_append, List.length_cons,
          List.length_nil]
        omega
      · intro x
        rw [Program.eval_append, hP x]
        have hI : Program.eval [(i₀, σ, σ)] x = σ := by
          simp [Program.eval, Instr.eval]
        rw [hI]
        cases hg : g.eval x <;> simp [Formula.eval, hg]
  | and g h ihg ihh =>
      intro σ hσ
      obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hcomm⟩ := exists_commutator hσ
      obtain ⟨P₁, hl₁, hP₁⟩ := ihg σ₁ hσ₁
      obtain ⟨P₂, hl₂, hP₂⟩ := ihh σ₂ hσ₂
      obtain ⟨P₃, hl₃, hP₃⟩ := ihg σ₁⁻¹ (isFiveCycle_inv hσ₁)
      obtain ⟨P₄, hl₄, hP₄⟩ := ihh σ₂⁻¹ (isFiveCycle_inv hσ₂)
      refine ⟨P₁ ++ P₂ ++ P₃ ++ P₄, ?_, ?_⟩
      · have e1 : (4 : ℕ) ^ g.depth ≤ 4 ^ (max g.depth h.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have e2 : (4 : ℕ) ^ h.depth ≤ 4 ^ (max g.depth h.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        simp only [Formula.depth, pow_succ, List.length_append]
        omega
      · intro x
        rw [Program.eval_append, Program.eval_append, Program.eval_append,
          hP₁ x, hP₂ x, hP₃ x, hP₄ x]
        cases hgx : g.eval x <;> cases hhx : h.eval x <;>
          simp [Formula.eval, hgx, hhx, ← hcomm, mul_assoc]

/-! ### Converse direction: programs to formulas -/

