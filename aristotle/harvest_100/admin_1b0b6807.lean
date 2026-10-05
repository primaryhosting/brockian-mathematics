import Mathlib

/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
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

/-- **Pell's equation for `d = 8`.** The equation `x² − 8·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`): take `(x, y) = (3, 1)`. -/
theorem pell_8 : ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine ⟨3, 1, by norm_num, by norm_num⟩

/-- The solutions of `x² − 8·y² = 1` generated from `(3, 1)` by the Brahmagupta
composition law: `(xₙ₊₁, yₙ₊₁) = (3xₙ + 8yₙ, xₙ + 3yₙ)`. -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (3, 1)
  | n + 1 => (3 * (pellSeq n).1 + 8 * (pellSeq n).2, (pellSeq n).1 + 3 * (pellSeq n).2)

/-- Every term of `pellSeq` solves `x² − 8·y² = 1`. -/
theorem pellSeq_sol (n : ℕ) : (pellSeq n).1 ^ 2 - 8 * (pellSeq n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih =>
      simp only [pellSeq]
      ring_nf
      ring_nf at ih
      linarith

/-- The second components of `pellSeq` are positive and strictly increasing;
in particular `x² − 8·y² = 1` has infinitely many integer solutions. -/
theorem pellSeq_snd_pos_strictMono :
    (∀ n : ℕ, 0 < (pellSeq n).1 ∧ 0 < (pellSeq n).2) ∧
      StrictMono fun n : ℕ => (pellSeq n).2 := by
  have hpos : ∀ n : ℕ, 0 < (pellSeq n).1 ∧ 0 < (pellSeq n).2 := by
    intro n
    induction n with
    | zero => norm_num [pellSeq]
    | succ n ih =>
        simp only [pellSeq]
        constructor <;> nlinarith [ih.1, ih.2]
  refine ⟨hpos, strictMono_nat_of_lt_succ ?_⟩
  intro n
  simp only [pellSeq]
  nlinarith [(hpos n).1, (hpos n).2]

/-- There are infinitely many integer solutions of `x² − 8·y² = 1`. -/
theorem pell_8_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 8 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => pellSeq n)
  · intro m n hmn
    simp only at hmn
    exact pellSeq_snd_pos_strictMono.2.injective (by rw [hmn])
  · intro n
    exact pellSeq_sol n

end Math

