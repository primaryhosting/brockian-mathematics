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

We formalise Barrington's theorem: the class of Boolean function families computed by
logarithmic-depth fan-in-two Boolean circuits (`NC¹`) coincides with the class of families
computed by polynomial-length width-`5` permutation branching programs.

* `CS.Barrington.Circuit` : fan-in two Boolean circuits over `{¬, ∧, ∨}` and constants.
* `CS.Barrington.Instr`, `CS.Barrington.run` : width-5 permutation branching programs,
  i.e. lists of instructions, each of which multiplies the running value in `S₅` by a
  permutation depending on (at most) one input bit.
* `CS.Barrington.NC1` and `CS.Barrington.W5BP` : the two classes.
* `CS.barrington` : the two classes are equal.
-/

namespace CS
namespace Barrington

open Equiv

/-- The symmetric group on five points. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-! ### Boolean circuits -/

/-- Fan-in two Boolean circuits (formulas) on `n` inputs. -/
inductive Circuit (n : ℕ) where
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- The Boolean function computed by a circuit. -/

lemma bigOr_eval {n : ℕ} (k : ℕ) (l : List (Circuit n)) (hl : l.length ≤ 2 ^ k)
    (x : Fin n → Bool) : (bigOr k l).eval x = l.any (fun c => c.eval x) := by
  induction k generalizing l with
  | zero =>
      rcases l with _ | ⟨c, l⟩
      · simp [bigOr, Circuit.eval]
      · rcases l with _ | ⟨d, l⟩
        · simp [bigOr]
        · simp at hl
  | succ k ih =>
      by_cases h : l.length ≤ 1
      · simp only [bigOr, if_pos h]
        rcases l with _ | ⟨c, l⟩
        · simp [Circuit.eval]
        · rcases l with _ | ⟨d, l⟩
          · simp
          · simp at h
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have ht : (l.take (l.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_take]
          omega
        have hd : (l.drop (l.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_drop]
          omega
        simp only [bigOr, if_neg h, Circuit.eval, ih _ ht, ih _ hd]
        conv_rhs => rw [← List.take_append_drop (l.length / 2) l]
        rw [List.any_append]

