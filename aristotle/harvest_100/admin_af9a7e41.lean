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
def configCount (q a b N : ℕ) : ℕ :=
  ((Finset.range N ×ˢ Finset.range N).filter
    (fun p => p.1 ≡ a [MOD q] ∧ p.2 ≡ b [MOD q])).card

/-- The expected main term for `configCount q a b N`, namely `N ^ 2 / q ^ 2`. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) ^ 2 / (q : ℝ) ^ 2

/-- The configuration count splits as a product of two one-dimensional counts. -/
lemma configCount_eq_mul (q a b N : ℕ) :
    configCount q a b N =
      Nat.count (fun x => x ≡ a [MOD q]) N * Nat.count (fun x => x ≡ b [MOD q]) N := by
  rw [configCount, Finset.filter_product (fun x => x ≡ a [MOD q]) (fun x => x ≡ b [MOD q]),
    Finset.card_product, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]

/-- The one-dimensional count in an arithmetic progression differs from its main term by
at most `1`. -/
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
theorem configCount_over_main_tendsto (q a b : ℕ) (hq : 0 < q) :
    Filter.Tendsto (fun N : ℕ => (configCount q a b N : ℝ) / mainTerm q N)
      Filter.atTop (nhds 1) := by
  have h := (count_mul_div_tendsto q a hq).mul (count_mul_div_tendsto q b hq)
  rw [mul_one] at h
  refine h.congr' (Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [configCount_eq_mul, mainTerm]
  push_cast
  field_simp

end EquidistributionBVReduction
end Brockian

