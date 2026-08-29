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

theorem exists_formula_entry (k : ℕ) : ∀ (P : Program n), P.length ≤ 2 ^ k → ∀ a b : Fin 5,
    ∃ φ : Formula n, φ.depth ≤ 6 * k + 1 ∧ ∀ x, ((φ.eval x = true) ↔ P.eval x a = b) := by
  induction k with
  | zero =>
      intro P hP a b
      match P with
      | [] =>
          refine ⟨.const (decide (a = b)), by simp [Formula.depth], ?_⟩
          intro x; simp [Formula.eval]
      | [(i, p, q)] =>
          have hev : ∀ x : Fin n → Bool,
              Program.eval [((i, p, q) : Instr n)] x a = if x i then p a else q a := by
            intro x
            by_cases hx : x i = true <;>
              simp [Program.eval, Instr.eval, hx]
          by_cases hp : p a = b <;> by_cases hq : q a = b
          · refine ⟨.const true, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.var i, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.not (.var i), by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
          · refine ⟨.const false, by simp [Formula.depth], ?_⟩
            intro x
            rw [hev x]
            by_cases hx : x i = true <;> simp [Formula.eval, hx, hp, hq]
      | I :: J :: t => simp at hP
  | succ k ih =>
      intro P hP a b
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow] at hP
      set m := P.length / 2 with hm
      have hL : (P.take m).length ≤ 2 ^ k := by
        rw [List.length_take]; omega
      have hR : (P.drop m).length ≤ 2 ^ k := by
        rw [List.length_drop]; omega
      obtain ⟨FR, hFRd, hFR⟩ : ∃ F : Fin 5 → Formula n, (∀ j, (F j).depth ≤ 6 * k + 1) ∧
          ∀ j x, (((F j).eval x = true) ↔ Program.eval (P.drop m) x a = j) := by
        choose F h1 h2 using fun j => ih (P.drop m) hR a j
        exact ⟨F, h1, h2⟩
      obtain ⟨FL, hFLd, hFL⟩ : ∃ F : Fin 5 → Formula n, (∀ j, (F j).depth ≤ 6 * k + 1) ∧
          ∀ j x, (((F j).eval x = true) ↔ Program.eval (P.take m) x j = b) := by
        choose F h1 h2 using fun j => ih (P.take m) hL j b
        exact ⟨F, h1, h2⟩
      refine ⟨or5 (fun j => .and (FR j) (FL j)), ?_, ?_⟩
      · have hd : ∀ j, ((Formula.and (FR j) (FL j)).depth) ≤ 6 * k + 2 := by
          intro j
          have h1 := hFRd j
          have h2 := hFLd j
          simp only [Formula.depth]
          omega
        have := or5_depth hd
        omega
      · intro x
        rw [or5_eval]
        have hsplit : P.take m ++ P.drop m = P := List.take_append_drop _ _
        constructor
        · rintro ⟨j, hj⟩
          simp only [Formula.eval, Bool.and_eq_true] at hj
          have h1 := (hFR j x).1 hj.1
          have h2 := (hFL j x).1 hj.2
          rw [← hsplit, Program.eval_append, Equiv.Perm.mul_apply, h1, h2]
        · intro hab
          refine ⟨Program.eval (P.drop m) x a, ?_⟩
          simp only [Formula.eval, Bool.and_eq_true]
          refine ⟨(hFR _ x).2 rfl, (hFL _ x).2 ?_⟩
          rw [← hsplit, Program.eval_append, Equiv.Perm.mul_apply] at hab
          exact hab

