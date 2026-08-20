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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a sequence `lam : ℕ → ℝ` of eigenvalues:
`spectralCounting lam t` is the number of indices `n` with `lam n ≤ t`.
(If that index set were infinite the `Set.ncard` would be `0`; under the escape
hypothesis used below the set is always finite.) -/

theorem counting_diverges_of_exists {lam : ℕ → ℝ}
    (hesc : ∀ t : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → t < lam n) :
    Filter.Tendsto (spectralCounting lam) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 (fun k => ?_)
  obtain ⟨t₀, ht₀⟩ := Finset.exists_le ((Finset.range k).image lam)
  filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
  have hsub : (↑(Finset.range k) : Set ℕ) ⊆ {n : ℕ | lam n ≤ t} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact le_trans (ht₀ _ (Finset.mem_image_of_mem lam (Finset.mem_range.2 hn))) ht
  have h := Set.ncard_le_ncard hsub (sublevel_finite hesc t)
  simpa [spectralCounting] using h

/-- Consequence: under the same escape hypothesis the counting function is unbounded. -/
