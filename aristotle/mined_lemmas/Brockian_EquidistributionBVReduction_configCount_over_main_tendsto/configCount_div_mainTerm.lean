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

theorem configCount_div_mainTerm (N : ℕ) (hN : 1 ≤ N) :
    (configCount N : ℝ) / mainTerm N = 1 + 1 / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : (2 : ℝ) * configCount N = (N : ℝ) * (N + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (two_mul_configCount N)
  unfold mainTerm
  field_simp
  nlinarith [h]

/-- **Config count over main term tends to one.**
The number of Bombieri–Vinogradov configurations of level `N`, divided by the main
term `N ^ 2 / 2`, tends to `1` as `N → ∞`. -/
