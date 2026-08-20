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

lemma prodCirc_eval {n : ℕ} (k : ℕ) (P : List (Instr n)) (hP : P.length ≤ 2 ^ k) (g : Perm5)
    (x : Fin n → Bool) : (prodCirc k P g).eval x = decide (run P x = g) := by
  induction k generalizing P g with
  | zero =>
      simpa [prodCirc] using baseCirc_eval P (by simpa using hP) g x
  | succ k ih =>
      by_cases h : P.length ≤ 1
      · simp only [prodCirc, if_pos h]
        exact baseCirc_eval P h g x
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have ht : (P.take (P.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_take]; omega
        have hd : (P.drop (P.length / 2)).length ≤ 2 ^ k := by
          rw [List.length_drop]; omega
        have hlen : (allPerms.map (fun h : Perm5 =>
            Circuit.and (prodCirc k (P.take (P.length / 2)) h)
              (prodCirc k (P.drop (P.length / 2)) (h⁻¹ * g)))).length ≤ 2 ^ 7 := by
          rw [List.length_map, allPerms_length]
          norm_num
        have hsplit : run P x = run (P.take (P.length / 2)) x * run (P.drop (P.length / 2)) x := by
          conv_lhs => rw [← List.take_append_drop (P.length / 2) P]
          rw [run_append]
        simp only [prodCirc, if_neg h]
        rw [bigOr_eval 7 _ hlen x, List.any_map]
        simp only [Function.comp_def, Circuit.eval, ih _ ht, ih _ hd]
        rw [hsplit]
        exact any_prod_eq _ _ x g

