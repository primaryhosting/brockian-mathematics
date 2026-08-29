import Mathlib

/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = e^{2πi/5}`. -/

lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_period, ih M (by omega), Nat.add_mod_right]

