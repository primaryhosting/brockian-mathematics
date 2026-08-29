import Mathlib

/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
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

/-- **Pell's equation for `d = 5`**: `x² - 5·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  The witness is `(x, y) = (9, 4)`. -/
theorem pell_5 : ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨9, 4, by norm_num, by norm_num⟩

/-- The step of the Pell recurrence for `d = 5`, given by multiplication by the
solution `9 + 4√5`. -/
def pellStep5 (p : ℤ × ℤ) : ℤ × ℤ := (9 * p.1 + 20 * p.2, 4 * p.1 + 9 * p.2)

/-- The sequence of Pell solutions obtained by iterating `pellStep5` from `(1, 0)`. -/
def pellSeq5 : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => pellStep5 (pellSeq5 n)

lemma pellSeq5_spec (n : ℕ) :
    (pellSeq5 n).1 ^ 2 - 5 * (pellSeq5 n).2 ^ 2 = 1 ∧ 1 ≤ (pellSeq5 n).1 ∧
      0 ≤ (pellSeq5 n).2 := by
  induction n with
  | zero => simp [pellSeq5]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pellSeq5, pellStep5] <;> nlinarith [h1, h2, h3]

lemma pellSeq5_snd_strictMono : StrictMono fun n => (pellSeq5 n).2 := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨_, h2, h3⟩ := pellSeq5_spec n
  simp only [pellSeq5, pellStep5]
  omega

/-- There are infinitely many integer solutions of `x² - 5·y² = 1`. -/
theorem pell_5_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 5 * p.2 ^ 2 = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => pellSeq5 n) (fun a b hab => ?_) (fun n => (pellSeq5_spec n).1)
  exact pellSeq5_snd_strictMono.injective (congrArg Prod.snd hab)

end Math

