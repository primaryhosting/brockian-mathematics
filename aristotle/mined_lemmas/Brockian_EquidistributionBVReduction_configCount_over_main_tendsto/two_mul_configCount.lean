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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical
open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The set of *configurations* of level `N` occurring in a Bombieri–Vinogradov style
reduction: pairs `(q, a)` consisting of a modulus `1 ≤ q ≤ N` together with a residue
class `a` modulo `q`. -/

theorem two_mul_configCount (N : ℕ) : 2 * configCount N = N * (N + 1) := by
  rw [configCount_eq_sum]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]
    ring

/-- For `N ≥ 1` the ratio of the configuration count to the main term is `1 + 1 / N`. -/
