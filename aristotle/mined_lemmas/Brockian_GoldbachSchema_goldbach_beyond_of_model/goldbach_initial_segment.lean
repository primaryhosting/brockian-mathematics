import Brockian.GoldbachSchema

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

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace GoldbachSchema

/-- The Goldbach property: `n` is a sum of two primes. -/

theorem goldbach_initial_segment (n : ℕ) (h4 : 4 ≤ n) (h100 : n ≤ 100) (hn : Even n) :
    IsGoldbach n := by
  have key : ∀ m ∈ Finset.Icc 4 100, Even m →
      ∃ p ∈ Finset.range (m + 1), ∃ q ∈ Finset.range (m + 1),
        Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by decide
  obtain ⟨p, _, q, _, hp, hq, hsum⟩ := key n (Finset.mem_Icc.mpr ⟨h4, h100⟩) hn
  exact ⟨p, q, hp, hq, hsum⟩

end GoldbachSchema
end Brockian

