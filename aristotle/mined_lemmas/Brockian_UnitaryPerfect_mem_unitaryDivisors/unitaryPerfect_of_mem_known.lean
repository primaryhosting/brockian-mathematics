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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to appear before any other syntax,
so the mandated header block is placed immediately after the single `import Mathlib` line.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd d (n / d) = 1`. -/

theorem unitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) : IsUnitaryPerfect n := by
  fin_cases hn
  · exact ⟨by norm_num, by rw [usigma_six]⟩
  · exact ⟨by norm_num, by rw [usigma_sixty]⟩
  · exact ⟨by norm_num, by rw [usigma_ninety]⟩
  · exact ⟨by norm_num, by rw [usigma_87360]⟩
  · exact ⟨by norm_num, by rw [usigma_fifth]⟩

/-- Unconditionally, there are at least five unitary perfect numbers. -/
