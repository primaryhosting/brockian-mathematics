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

lemma sum_bin (x : ℕ → ℝ) (g : ℝ → ℝ) (N k : ℕ) (hk : 0 < k) :
    ∑ j ∈ Finset.range k, ∑ n ∈ bin x N k j, g (Int.fract (x n))
      = ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hmaps : ∀ n ∈ Finset.range N, ⌊(k:ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range k := by
    intro n _
    have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) :=
      mul_nonneg (le_of_lt hk0) (Int.fract_nonneg _)
    have h1 : (k:ℝ) * Int.fract (x n) < k := by
      have := Int.fract_lt_one (x n)
      nlinarith
    simpa [Finset.mem_range] using (Nat.floor_lt h0).2 (by exact_mod_cast h1)
  have hfiber : ∀ j : ℕ,
      ((Finset.range N).filter (fun n => ⌊(k:ℝ) * Int.fract (x n)⌋₊ = j)) = bin x N k j := by
    intro j
    ext n
    simp only [bin, Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) :=
      mul_nonneg (le_of_lt hk0) (Int.fract_nonneg _)
    rw [Nat.floor_eq_iff h0]
    constructor
    · rintro ⟨hl, hr⟩
      constructor
      · rw [div_le_iff₀ hk0]; linarith [hl]
      · rw [lt_div_iff₀ hk0]; linarith [hr]
    · rintro ⟨hl, hr⟩
      rw [div_le_iff₀ hk0] at hl
      rw [lt_div_iff₀ hk0] at hr
      constructor <;> linarith
  calc ∑ j ∈ Finset.range k, ∑ n ∈ bin x N k j, g (Int.fract (x n))
      = ∑ j ∈ Finset.range k,
          ∑ n ∈ (Finset.range N).filter (fun n => ⌊(k:ℝ) * Int.fract (x n)⌋₊ = j),
            g (Int.fract (x n)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hfiber j]
    _ = ∑ n ∈ Finset.range N, g (Int.fract (x n)) :=
        Finset.sum_fiberwise_of_maps_to hmaps _

/-- The cardinality of a bin is the increment of the empirical counting function. -/
