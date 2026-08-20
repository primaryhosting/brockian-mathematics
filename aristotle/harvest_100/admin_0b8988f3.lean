/-
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 3`**: `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  The fundamental solution is `(x, y) = (2, 1)`. -/
theorem pell_3 : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 :=
  ⟨2, 1, by norm_num, one_ne_zero⟩

/-- The same statement obtained from Mathlib's general theory of Pell's equation,
`Pell.exists_of_not_isSquare`, which produces a nontrivial solution of `x² − d·y² = 1`
for any positive non-square `d`. -/
theorem pell_3' : ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = 1 ∧ y ≠ 0 := by
  refine Pell.exists_of_not_isSquare (by norm_num) ?_
  rintro ⟨r, hr⟩
  have h1 : r ≤ 2 := by nlinarith
  have h2 : -2 ≤ r := by nlinarith
  interval_cases r <;> omega

/-- The sequence of solutions generated from `(2, 1)` by the fundamental automorphism
`(x, y) ↦ (2x + 3y, x + 2y)` of `x² − 3y² = 1` (multiplication by `2 + √3`). -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => (2 * (pellSeq n).1 + 3 * (pellSeq n).2, (pellSeq n).1 + 2 * (pellSeq n).2)

lemma pellSeq_sol (n : ℕ) : (pellSeq n).1 ^ 2 - 3 * (pellSeq n).2 ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih => simp only [pellSeq]; ring_nf; ring_nf at ih; linarith

lemma pellSeq_le (n : ℕ) : 2 ≤ (pellSeq n).1 ∧ 1 ≤ (pellSeq n).2 := by
  induction n with
  | zero => norm_num [pellSeq]
  | succ n ih => simp only [pellSeq]; omega

lemma pellSeq_snd_strictMono : StrictMono fun n => (pellSeq n).2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have := pellSeq_le n
  simp only [pellSeq]
  omega

/-- There are infinitely many integer solutions of `x² − 3y² = 1`. -/
theorem pell_3_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 3 * p.2 ^ 2 = 1}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := pellSeq)
    (fun m n h => pellSeq_snd_strictMono.injective (congrArg Prod.snd h))
    (fun n => pellSeq_sol n)

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

