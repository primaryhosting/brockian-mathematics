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

/-
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- The finite set of *Goldbach representations* of `n`: those `p ≤ n` such that both `p`
and `n - p` are prime. -/

theorem goldbach_of_model_of_bound_le (M : Model) (hb : M.bound ≤ 202) (n : ℕ)
    (h4 : 4 ≤ n) (hev : Even n) : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  by_cases h : n ≤ 200
  · exact goldbach_small n h4 h hev
  · refine goldbach_beyond_of_model M n (le_trans hb ?_) hev
    obtain ⟨k, hk⟩ := hev
    omega

end GoldbachSchema
end Brockian

