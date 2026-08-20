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

lemma any_prod_eq {n : ℕ} (T D : List (Instr n)) (x : Fin n → Bool) (g : Perm5) :
    (allPerms.any fun h => decide (run T x = h) && decide (run D x = h⁻¹ * g))
      = decide (run T x * run D x = g) := by
  refine Bool.eq_iff_iff.mpr ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [List.any_eq_true] at hb
    obtain ⟨h, -, hh⟩ := hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    simp [hh.1, hh.2]
  · simp only [decide_eq_true_eq] at hb
    rw [List.any_eq_true]
    refine ⟨run T x, mem_allPerms _, ?_⟩
    have hD : run D x = (run T x)⁻¹ * g := by rw [← hb]; group
    simp [hD]

/-- A circuit deciding whether the program `P` (of length at most `2 ^ k`) outputs `g`. -/
