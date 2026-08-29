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

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem isUnitaryPerfect_largestKnown : IsUnitaryPerfect largestKnown := by
  refine ⟨by norm_num [largestKnown], ?_⟩
  rw [usigma_of_list (N := largestKnown)
    (l := [2 ^ 18, 3, 5 ^ 4, 7, 11, 13, 19, 37, 79, 109, 157, 313]) (by norm_num [largestKnown])
    ?_ ?_]
  · norm_num [largestKnown]
  · rintro x hx
    fin_cases hx
    · exact ⟨2, 18, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨19, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨37, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨79, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨109, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨157, 1, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨313, 1, by norm_num, by norm_num, by norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil]
    norm_num [Nat.Coprime]

/-! ## The set of known unitary perfect numbers -/

/-- The five known unitary perfect numbers. -/
