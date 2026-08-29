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

lemma abs_count_sub_le_one (q a N : ℕ) (hq : 0 < q) :
    |(Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) - (N : ℝ) / q| ≤ 1 := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hd : (q : ℝ) * ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N q
  have hm : ((N % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt _ hq
  have hm0 : (0 : ℝ) ≤ ((N % q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNq : (N : ℝ) / (q : ℝ) = ((N / q : ℕ) : ℝ) + ((N % q : ℕ) : ℝ) / (q : ℝ) := by
    field_simp
    linarith
  have hr0 : (0 : ℝ) ≤ ((N % q : ℕ) : ℝ) / (q : ℝ) := div_nonneg hm0 hq'.le
  have hr1 : ((N % q : ℕ) : ℝ) / (q : ℝ) < 1 := (div_lt_one hq').2 hm
  rw [Nat.count_modEq_card N hq a, hNq]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- The normalized one-dimensional count tends to `1`. -/
