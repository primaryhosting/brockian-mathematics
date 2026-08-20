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

lemma prodCirc_depth {n : ℕ} (k : ℕ) (P : List (Instr n)) (g : Perm5) :
    (prodCirc k P g).depth ≤ 11 * k + 3 := by
  induction k generalizing P g with
  | zero => simpa [prodCirc] using baseCirc_depth P g
  | succ k ih =>
      by_cases h : P.length ≤ 1
      · simp only [prodCirc, if_pos h]
        have := baseCirc_depth P g
        omega
      · simp only [prodCirc, if_neg h]
        have hb := bigOr_depth (n := n) 7
          (allPerms.map (fun h : Perm5 =>
            Circuit.and (prodCirc k (P.take (P.length / 2)) h)
              (prodCirc k (P.drop (P.length / 2)) (h⁻¹ * g)))) (11 * k + 4) ?_
        · omega
        · intro c hc
          rw [List.mem_map] at hc
          obtain ⟨h', _, rfl⟩ := hc
          have h1 := ih (P.take (P.length / 2)) h'
          have h2 := ih (P.drop (P.length / 2)) (h'⁻¹ * g)
          simp only [Circuit.depth]
          omega

/-! ### The two directions -/

