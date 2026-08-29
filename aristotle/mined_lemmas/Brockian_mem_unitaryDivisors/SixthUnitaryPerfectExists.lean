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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem SixthUnitaryPerfectExists
    (h : ∃ N, IsUnitaryPerfect N ∧
      N ∉ ({6, 60, 90, 87360, 146361946186458562560000} : Finset ℕ)) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ n ∈ S, IsUnitaryPerfect n := by
  obtain ⟨N, hN, hNmem⟩ := h
  refine ⟨insert N {6, 60, 90, 87360, 146361946186458562560000}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hNmem]
    decide
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hN
    · exact isUnitaryPerfect_six
    · exact isUnitaryPerfect_sixty
    · exact isUnitaryPerfect_ninety
    · exact isUnitaryPerfect_87360
    · exact isUnitaryPerfect_big

end UnitaryPerfect
end Brockian

