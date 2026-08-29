/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires all `import`
-- commands to precede any module docstring.)

import Mathlib

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies the class `NC¹` (Boolean formulas of
logarithmic depth) with the class of functions computed by *width-5 permutation branching
programs* of polynomial length.

* `CS.Formula n` are Boolean formulas in the variables `Fin n` built from `¬`, `∧`, `∨`.
  Following the usual convention for Barrington's theorem, `Formula.depth` counts the
  nesting depth of the binary gates (negations are free, since they can be pushed to the
  leaves without changing the depth).
* `CS.BProg n` is a *width-5 permutation branching program*: a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5`, depending on the
  value of that bit.  The value `BProg.eval P x` of the program on the input `x` is the
  product of the permutations selected by the instructions.

The two halves of `CS.barrington` are:

1. every formula of depth `d` is computed by a width-5 permutation branching program of
   length at most `4 ^ d`, with output the prescribed 5-cycle `σ` on accepted inputs and the
   identity on rejected inputs (this is Barrington's construction);
2. conversely, for every width-5 permutation branching program `P` of length `ℓ` and every
   target permutation `σ`, the acceptance predicate `P.eval x = σ` is computed by a formula of
   depth `O(log ℓ)` (a balanced divide-and-conquer evaluation of the product).
-/

namespace CS

open Equiv Equiv.Perm

/-- The group of permutations of five points: the "width 5" of Barrington's theorem. -/
abbrev W : Type := Equiv.Perm (Fin 5)

/-! ### Boolean formulas -/

/-- Boolean formulas over the variables `Fin n`. -/
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n

/-- The depth of a formula, counting binary gates only (negations are free). -/

theorem exists_prog {n : ℕ} (F : Formula n) :
    ∀ σ : W, σ.cycleType = {5} →
      ∃ P : BProg n, P ≠ [] ∧ P.length ≤ 4 ^ F.depth ∧
        ∀ x, P.eval x = if F.eval x then σ else 1 := by
  induction F with
  | var i =>
      intro σ _
      refine ⟨[⟨i, 1, σ⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      simp only [BProg.eval_cons, BProg.eval_nil, mul_one, Instr.val, Formula.eval]
      cases x i <;> simp
  | neg F ih =>
      intro σ hσ
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ih σ⁻¹ (by rw [cycleType_inv]; exact hσ)
      refine ⟨BProg.lmul σ Q, BProg.lmul_ne_nil σ hQne, by simpa [Formula.depth] using hQlen, ?_⟩
      intro x
      rw [BProg.eval_lmul σ hQne, hQ]
      simp only [Formula.eval]
      cases F.eval x <;> simp
  | conj F G ihF ihG =>
      intro σ hσ
      obtain ⟨P, hPne, hPlen, hP⟩ := ihF sigma0 sigma0_cycleType
      obtain ⟨Q, hQne, hQlen, hQ⟩ := ihG tau0 tau0_cycleType
      have key := comm_prog hP hQ
      obtain ⟨R, hRlen, hRne, hR⟩ :=
        relabel key (isConj_iff_cycleType_eq.2 (by rw [comm_cycleType, hσ]))
      refine ⟨R, hRne (by simp [hPne]), ?_, hR⟩
      rw [hRlen]
      have h1 : P.length ≤ 4 ^ (max F.depth G.depth) :=
        hPlen.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : Q.length ≤ 4 ^ (max F.depth G.depth) :=
        hQlen.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : (P ++ Q ++ P.inv ++ Q.inv).length = 2 * (P.length + Q.length) := by
        simp [BProg.length_inv]; ring
      rw [this]
      show 2 * (P.length + Q.length) ≤ 4 ^ (max F.depth G.depth + 1)
      rw [pow_succ]
      omega
  | disj F G ihF ihG =>
      intro σ hσ
      -- programs for the negations
      obtain ⟨P0, hP0ne, hP0len, hP0⟩ := ihF sigma0⁻¹ (by rw [cycleType_inv]; exact sigma0_cycleType)
      obtain ⟨Q0, hQ0ne, hQ0len, hQ0⟩ := ihG tau0⁻¹ (by rw [cycleType_inv]; exact tau0_cycleType)
      set P := BProg.lmul sigma0 P0 with hPdef
      set Q := BProg.lmul tau0 Q0 with hQdef
      have hPne : P ≠ [] := BProg.lmul_ne_nil _ hP0ne
      have hQne : Q ≠ [] := BProg.lmul_ne_nil _ hQ0ne
      have hP : ∀ x, P.eval x = if (!F.eval x) then sigma0 else 1 := by
        intro x
        rw [hPdef, BProg.eval_lmul sigma0 hP0ne, hP0]
        cases F.eval x <;> simp
      have hQ : ∀ x, Q.eval x = if (!G.eval x) then tau0 else 1 := by
        intro x
        rw [hQdef, BProg.eval_lmul tau0 hQ0ne, hQ0]
        cases G.eval x <;> simp
      have key := comm_prog hP hQ
      obtain ⟨R, hRlen, hRne, hR⟩ :=
        relabel key (isConj_iff_cycleType_eq.2
          (by rw [comm_cycleType, cycleType_inv]; exact hσ.symm))
      have hRne' : R ≠ [] := hRne (by simp [hPne])
      refine ⟨BProg.lmul σ R, BProg.lmul_ne_nil σ hRne', ?_, ?_⟩
      · rw [BProg.length_lmul, hRlen]
        have h1 : P.length ≤ 4 ^ (max F.depth G.depth) := by
          rw [hPdef, BProg.length_lmul]
          exact hP0len.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
        have h2 : Q.length ≤ 4 ^ (max F.depth G.depth) := by
          rw [hQdef, BProg.length_lmul]
          exact hQ0len.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        have : (P ++ Q ++ P.inv ++ Q.inv).length = 2 * (P.length + Q.length) := by
          simp [BProg.length_inv]; ring
        rw [this]
        show 2 * (P.length + Q.length) ≤ 4 ^ (max F.depth G.depth + 1)
        rw [pow_succ]
        omega
      · intro x
        rw [BProg.eval_lmul σ hRne', hR]
        simp only [Formula.eval]
        cases F.eval x <;> cases G.eval x <;> simp

/-! ### The converse: evaluating a branching program by a shallow formula -/

/-- The constantly false formula (of depth 1). -/
