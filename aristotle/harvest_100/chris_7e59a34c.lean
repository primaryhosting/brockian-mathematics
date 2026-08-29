import Mathlib

/-!
# Pell 13, strengthened

A Mathlib-based companion to `Math.pell_13`: the solution set of `x² - 13·y² = 1`
in `ℤ × ℤ` is infinite, obtained by iterating the fundamental solution `(649, 180)`.
-/

namespace Math

/-- One step of multiplication by the fundamental unit `649 + 180·√13`. -/
def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (649 * p.1 + 2340 * p.2, 180 * p.1 + 649 * p.2)

/-- The `n`-th power of the fundamental solution `(649, 180)`, starting from `(1, 0)`. -/
def pellSol : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep (pellSol n)

lemma pellSol_isSol (n : ℕ) : (pellSol n).1 ^ 2 - 13 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
      simp only [pellSol, pellStep]
      nlinarith [ih]

lemma pellSol_nonneg (n : ℕ) : 0 ≤ (pellSol n).1 ∧ 0 ≤ (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [pellSol, pellStep]
      constructor <;> positivity

lemma pellSol_fst_pos (n : ℕ) : 1 ≤ (pellSol n).1 := by
  have h0 := (pellSol_nonneg n).1
  have h2 := (pellSol_nonneg n).2
  have h := pellSol_isSol n
  nlinarith [sq_nonneg (pellSol n).2]

lemma pellSol_snd_strictMono : StrictMono fun n => (pellSol n).2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 := pellSol_fst_pos n
  have h2 := (pellSol_nonneg n).2
  simp only [pellSol, pellStep]
  nlinarith

/-- The set of integer solutions of `x² - 13·y² = 1` is infinite. -/
theorem pell_13_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 13 * p.2 ^ 2 = 1}.Infinite := by
  have hinj : Function.Injective pellSol := by
    intro m n hmn
    exact pellSol_snd_strictMono.injective (congrArg Prod.snd hmn)
  have hrange : Set.range pellSol ⊆ {p : ℤ × ℤ | p.1 ^ 2 - 13 * p.2 ^ 2 = 1} := by
    rintro p ⟨n, rfl⟩
    exact pellSol_isSol n
  exact Set.Infinite.mono hrange (Set.infinite_range_of_injective hinj)

end Math

/-!
# Pell 13
Category: Pure Mathematics
Target: Math.pell_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 13`.**
`x² - 13·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(equivalently, a solution other than `(±1, 0)`).
The fundamental solution is `(x, y) = (649, 180)`:
`649² = 421201 = 13 · 180² + 1 = 13 · 32400 + 1`. -/
theorem pell_13 : ∃ x y : Int, y ≠ 0 ∧ x ^ 2 - 13 * y ^ 2 = 1 :=
  ⟨649, 180, by decide, by decide⟩

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

