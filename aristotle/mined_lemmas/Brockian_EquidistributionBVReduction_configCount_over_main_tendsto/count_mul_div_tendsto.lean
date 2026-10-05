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

lemma count_mul_div_tendsto (q a : ℕ) (hq : 0 < q) :
    Filter.Tendsto
      (fun N : ℕ => (Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) * (q : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have key : ∀ N : ℕ, 1 ≤ N →
      |(Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) * (q : ℝ) / (N : ℝ) - 1| ≤ (q : ℝ) / N := by
    intro N hN
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h := abs_count_sub_le_one q a N hq
    have hrw : (Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) * (q : ℝ) / (N : ℝ) - 1
        = ((Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) - (N : ℝ) / q) * ((q : ℝ) / N) := by
      field_simp
    rw [hrw, abs_mul, abs_of_nonneg (div_nonneg hq'.le hN'.le)]
    have hpos : (0 : ℝ) ≤ (q : ℝ) / N := div_nonneg hq'.le hN'.le
    nlinarith [abs_nonneg ((Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) - (N : ℝ) / q)]
  have hzero : Filter.Tendsto (fun N : ℕ => (q : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hsq := squeeze_zero' (f := fun N : ℕ =>
      |(Nat.count (fun x => x ≡ a [MOD q]) N : ℝ) * (q : ℝ) / (N : ℝ) - 1|)
    (g := fun N : ℕ => (q : ℝ) / (N : ℝ))
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    (Filter.eventually_atTop.2 ⟨1, fun N hN => key N hN⟩) hzero
  have h2 := (tendsto_zero_iff_abs_tendsto_zero _).2 hsq
  simpa using h2.add_const (1 : ℝ)

/-- A quantitative form of the equidistribution statement: the configuration count differs
from the main term `N ^ 2 / q ^ 2` by at most `2 * (N / q) + 1`. -/
