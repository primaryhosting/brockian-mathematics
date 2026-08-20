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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- A *Landau prime* is a prime of the form `n ^ 2 + 1`. -/

theorem landauCountUnbounded_of_hardyLittlewood (h : HardyLittlewoodLowerBound) :
    LandauCountUnbounded := by
  obtain ⟨c, hc, hbound⟩ := h
  intro B
  have htend : Filter.Tendsto (fun n : ℕ => c * ((n : ℝ) / Real.log n))
      Filter.atTop Filter.atTop :=
    ((tendsto_id_div_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc)
  have hev := (htend.eventually_ge_atTop ((B : ℝ) + 1)).and hbound
  obtain ⟨x, hx1, hx2⟩ := hev.exists
  have hlt : (B : ℝ) < (landauCount x : ℝ) := by linarith
  exact ⟨x, by exact_mod_cast hlt⟩

/-- **Conditional Landau fourth conjecture from Hardy–Littlewood.**  If the Hardy–Littlewood
lower bound for the counting function of `n ^ 2 + 1` holds, then there are infinitely many
primes of the form `n ^ 2 + 1`. -/
