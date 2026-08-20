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

lemma bigOr_depth {n : ℕ} (k : ℕ) (l : List (Circuit n)) (D : ℕ)
    (hD : ∀ c ∈ l, c.depth ≤ D) : (bigOr k l).depth ≤ D + k := by
  induction k generalizing l with
  | zero =>
      rcases l with _ | ⟨c, l⟩
      · simp [bigOr, Circuit.depth]
      · simpa [bigOr] using hD c (by simp)
  | succ k ih =>
      by_cases h : l.length ≤ 1
      · simp only [bigOr, if_pos h]
        rcases l with _ | ⟨c, l⟩
        · simp [Circuit.depth]
        · have := hD c (by simp)
          simpa using by omega
      · have ht : ∀ c ∈ l.take (l.length / 2), c.depth ≤ D := fun c hc =>
          hD c ((List.take_sublist _ _).mem hc)
        have hdr : ∀ c ∈ l.drop (l.length / 2), c.depth ≤ D := fun c hc =>
          hD c ((List.drop_sublist _ _).mem hc)
        have h1 := ih (l.take (l.length / 2)) ht
        have h2 := ih (l.drop (l.length / 2)) hdr
        simp only [bigOr, if_neg h, Circuit.depth]
        omega

/-- The base case: a circuit deciding whether a program of length at most one outputs `g`. -/
