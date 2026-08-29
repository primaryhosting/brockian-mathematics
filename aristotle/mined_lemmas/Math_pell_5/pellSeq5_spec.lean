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

lemma pellSeq5_spec (n : ℕ) :
    (pellSeq5 n).1 ^ 2 - 5 * (pellSeq5 n).2 ^ 2 = 1 ∧ 1 ≤ (pellSeq5 n).1 ∧
      0 ≤ (pellSeq5 n).2 := by
  induction n with
  | zero => simp [pellSeq5]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pellSeq5, pellStep5] <;> nlinarith [h1, h2, h3]

