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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma trap_integral_lower {a b d : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a + d ≤ b - d) :
    b - a - 2 * d ≤ ∫ t in (0:ℝ)..1, trap a b d t := by
  have hcont : Continuous (trap a b d) := trap_continuous a b d
  have hint : ∀ u v : ℝ, IntervalIntegrable (trap a b d) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  have h1 : (0:ℝ) ≤ a + d := by linarith
  have h2 : b - d ≤ 1 := by linarith
  have hsplit : (∫ t in (0:ℝ)..1, trap a b d t) =
      (∫ t in (0:ℝ)..(a + d), trap a b d t) + (∫ t in (a + d)..(b - d), trap a b d t)
        + (∫ t in (b - d)..1, trap a b d t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmid : (∫ t in (a + d)..(b - d), trap a b d t) = b - d - (a + d) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact trap_eq_one hd ht.1 ht.2
  have hleft : (0:ℝ) ≤ ∫ t in (0:ℝ)..(a + d), trap a b d t :=
    intervalIntegral.integral_nonneg h1 (fun t _ => trap_nonneg _ _ _ _)
  have hright : (0:ℝ) ≤ ∫ t in (b - d)..1, trap a b d t :=
    intervalIntegral.integral_nonneg h2 (fun t _ => trap_nonneg _ _ _ _)
  rw [hsplit, hmid]
  linarith

