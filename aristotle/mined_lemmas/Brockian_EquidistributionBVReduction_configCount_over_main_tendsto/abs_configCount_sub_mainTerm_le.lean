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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of "configurations" below `N` for the modulus `q` and the residues `a`, `b`:
the pairs `(m, n)` with `m, n < N`, `m ≡ a [MOD q]` and `n ≡ b [MOD q]`. -/

theorem abs_configCount_sub_mainTerm_le (q a b N : ℕ) (hq : 0 < q) :
    |(configCount q a b N : ℝ) - mainTerm q N| ≤ 2 * ((N : ℝ) / q) + 1 := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hx : (0 : ℝ) ≤ (N : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hq'.le
  have h1 := abs_count_sub_le_one q a N hq
  have h2 := abs_count_sub_le_one q b N hq
  rw [abs_le] at h1 h2
  have hmain : mainTerm q N = ((N : ℝ) / q) ^ 2 := by
    rw [mainTerm, div_pow]
  rw [configCount_eq_mul, hmain, abs_le]
  push_cast
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **Equidistribution of configurations in arithmetic progressions.**
The number of pairs `(m, n)` with `m, n < N`, `m ≡ a [MOD q]`, `n ≡ b [MOD q]`, divided by
the main term `N ^ 2 / q ^ 2`, tends to `1` as `N → ∞`. -/
