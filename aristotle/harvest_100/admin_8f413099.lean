import Mathlib

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- The standard recursion generating solutions of `x² - 3y² = 1` from the
fundamental solution `(2, 1)`: `(x, y) ↦ (2x + 3y, x + 2y)`. -/
def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (2 * p.1 + 3 * p.2, p.1 + 2 * p.2)

/-- The `n`-th solution of `x² - 3y² = 1` obtained by iterating `pellStep`
starting from `(2, 1)`. -/
def pellSol : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => pellStep (pellSol n)

lemma pellStep_spec (p : ℤ × ℤ) (h : p.1 ^ 2 - 3 * p.2 ^ 2 = 1) :
    (pellStep p).1 ^ 2 - 3 * (pellStep p).2 ^ 2 = 1 := by
  simp only [pellStep]
  nlinarith [h]

lemma pellSol_spec (n : ℕ) : (pellSol n).1 ^ 2 - 3 * (pellSol n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih => exact pellStep_spec _ ih

lemma pellSol_pos (n : ℕ) : 0 < (pellSol n).1 ∧ 0 < (pellSol n).2 := by
  induction n with
  | zero => norm_num [pellSol]
  | succ n ih => exact ⟨by simp only [pellSol, pellStep]; omega,
      by simp only [pellSol, pellStep]; omega⟩

lemma pellSol_lt_succ (n : ℕ) : (pellSol n).2 < (pellSol (n + 1)).2 := by
  have := pellSol_pos n
  simp only [pellSol, pellStep]
  omega

lemma pellSol_strictMono : StrictMono fun n => (pellSol n).2 :=
  strictMono_nat_of_lt_succ pellSol_lt_succ

/-- **Pell's equation for `d = 3`.** The equation `x² - 3y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0`. -/
theorem pell_3 : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- In fact `x² - 3y² = 1` has infinitely many solutions in positive integers. -/
theorem pell_3_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 3 * p.2 ^ 2 = 1 ∧ 0 < p.1 ∧ 0 < p.2}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => pellSol n)
  case hi =>
    intro a b hab
    exact pellSol_strictMono.injective (congrArg Prod.snd hab)
  case hf =>
    intro n
    exact ⟨pellSol_spec n, (pellSol_pos n).1, (pellSol_pos n).2⟩

end Math

