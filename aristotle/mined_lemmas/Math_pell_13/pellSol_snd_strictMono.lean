import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/

lemma pellSol_snd_strictMono : StrictMono fun n => (pellSol n).2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 := pellSol_fst_pos n
  have h2 := (pellSol_nonneg n).2
  simp only [pellSol, pellStep]
  nlinarith

/-- The set of integer solutions of `x² - 13·y² = 1` is infinite. -/
