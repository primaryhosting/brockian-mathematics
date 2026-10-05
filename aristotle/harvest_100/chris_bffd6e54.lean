/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 2·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, a solution other than `(±1, 0)`).
Witness: `3² − 2·2² = 9 − 8 = 1`. -/
theorem pell_2 : ∃ x y : Int, x ^ 2 - 2 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨3, 2, by decide, by decide⟩

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

import Mathlib
import RequestProject.Pell2

/-!
# Infinitely many solutions of the Pell equation `x² − 2·y² = 1`

A strengthening of `Math.pell_2`: the solution set of `x² − 2·y² = 1` over `ℤ`
is infinite, obtained by iterating `(x, y) ↦ (3x + 4y, 2x + 3y)`
(multiplication by the fundamental unit `3 + 2√2`).
-/

namespace Math

/-- The iterates of `(x, y) ↦ (3x + 4y, 2x + 3y)` starting from `(1, 0)`. -/
def pellStep : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pellStep n).1 + 4 * (pellStep n).2, 2 * (pellStep n).1 + 3 * (pellStep n).2)

theorem pellStep_sol (n : ℕ) : (pellStep n).1 ^ 2 - 2 * (pellStep n).2 ^ 2 = 1 := by
  induction n with
  | zero => simp [pellStep]
  | succ n ih => rw [pellStep]; ring_nf; ring_nf at ih; linarith

theorem pellStep_bounds (n : ℕ) :
    1 ≤ (pellStep n).1 ∧ 0 ≤ (pellStep n).2 ∧ (pellStep n).1 < (pellStep (n + 1)).1 := by
  induction n with
  | zero => refine ⟨by simp [pellStep], by simp [pellStep], by simp [pellStep]⟩
  | succ n ih =>
    obtain ⟨h1, h2, _⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pellStep] <;> linarith

/-- The set of integer solutions of `x² − 2·y² = 1` is infinite. -/
theorem pell_2_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = 1}.Infinite := by
  have hstrict : StrictMono fun n => (pellStep n).1 :=
    strictMono_nat_of_lt_succ fun n => (pellStep_bounds n).2.2
  have hinj : Function.Injective pellStep := fun a b hab =>
    hstrict.injective (by rw [hab])
  exact Set.infinite_of_injective_forall_mem hinj (fun n => pellStep_sol n)

end Math

