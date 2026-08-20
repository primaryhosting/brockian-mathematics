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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
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

set_option grind.warning false

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part is `< a`. -/

lemma card_bin (x : ℕ → ℝ) (N k j : ℕ) (hk : 0 < k) :
    ((bin x N k j).card : ℝ)
      = (countBelow x N (((j:ℝ)+1)/k) : ℝ) - (countBelow x N ((j:ℝ)/k) : ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hle : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by
    rw [div_le_div_iff_of_pos_right hk0]
    linarith
  have hsub : (Finset.range N).filter (fun n => Int.fract (x n) < (j:ℝ)/k) ⊆
      (Finset.range N).filter (fun n => Int.fract (x n) < ((j:ℝ)+1)/k) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 hle⟩
  have hbin : bin x N k j =
      ((Finset.range N).filter (fun n => Int.fract (x n) < ((j:ℝ)+1)/k)) \
      ((Finset.range N).filter (fun n => Int.fract (x n) < (j:ℝ)/k)) := by
    ext n
    simp only [bin, Finset.mem_filter, Finset.mem_sdiff, not_and, not_lt]
    constructor
    · rintro ⟨hn, hl, hr⟩
      exact ⟨⟨hn, hr⟩, fun _ => hl⟩
    · rintro ⟨⟨hn, hr⟩, h2⟩
      exact ⟨hn, h2 hn, hr⟩
  have hcard : (bin x N k j).card = countBelow x N (((j:ℝ)+1)/k) - countBelow x N ((j:ℝ)/k) := by
    rw [hbin, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
    rfl
  have hcle : countBelow x N ((j:ℝ)/k) ≤ countBelow x N (((j:ℝ)+1)/k) :=
    Finset.card_le_card hsub
  rw [hcard, Nat.cast_sub hcle]

/-- The subdivision points `j/k` lie in `[0,1]`. -/
