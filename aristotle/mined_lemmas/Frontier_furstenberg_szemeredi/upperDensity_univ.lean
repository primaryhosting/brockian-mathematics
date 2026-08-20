/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

namespace Frontier

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/

theorem upperDensity_univ : upperDensity (Set.univ : Set ℕ) = 1 := by
  have h : (fun n : ℕ => (count Set.univ n : ℝ) / n) =ᶠ[Filter.atTop] fun _ => (1 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hc : count Set.univ n = n := by simp [count]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [hc]
    field_simp
  rw [upperDensity, Filter.limsup_congr h]
  exact Filter.limsup_const 1

end Density

/-- Base case (length three): every set of naturals of positive upper density contains a
three-term arithmetic progression with positive common difference. This is Roth's theorem,
applied along a sequence of scales of density at least `ε`. -/
