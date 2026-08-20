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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`. -/

theorem eventually_half_le_counting_of_WeylLawMatch
    {S : Set ℝ} {C d : ℝ} (hW : WeylLawMatch S C d) :
    ∀ᶠ Λ : ℝ in atTop, (C / 2) * Λ ^ (d / 2) ≤ (counting S Λ : ℝ) := by
  obtain ⟨hC, hd, hlim⟩ := hW
  have h1 : ∀ᶠ Λ : ℝ in atTop,
      (1 : ℝ) / 2 < (counting S Λ : ℝ) / (C * Λ ^ (d / 2)) := by
    have : Set.Ioi ((1 : ℝ) / 2) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by norm_num)
    exact hlim this
  filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with Λ hΛ hΛ0
  have hpow : (0 : ℝ) < Λ ^ (d / 2) := Real.rpow_pos_of_pos hΛ0 _
  have hden : (0 : ℝ) < C * Λ ^ (d / 2) := mul_pos hC hpow
  rw [lt_div_iff₀ hden] at hΛ
  nlinarith [hΛ, hpow, hC]

/-- The dominating function `(C / 2) * Λ ^ (d / 2)` tends to infinity. -/
