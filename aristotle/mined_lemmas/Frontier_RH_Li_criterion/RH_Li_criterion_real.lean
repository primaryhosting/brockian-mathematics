/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Filter Metric

namespace Frontier

/-- The `n`-th Li coefficient attached to a (finite) multiset `Z` of "zeros":
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/

theorem RH_Li_criterion_real (Z : Multiset ℂ) (h0 : (0 : ℂ) ∉ Z)
    (hfe : Z.map (fun ρ => 1 - ρ) = Z) (hconj : Z.map (starRingEnd ℂ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → ∃ l : ℝ, 0 ≤ l ∧ liCoeff Z n = (l : ℂ) := by
  constructor
  · intro hline n hn
    refine ⟨(liCoeff Z n).re, (RH_Li_criterion Z h0 hfe).mp hline n hn, ?_⟩
    apply Complex.ext <;> simp [liCoeff_im_eq_zero Z hconj n]
  · intro h
    refine (RH_Li_criterion Z h0 hfe).mpr ?_
    intro n hn
    obtain ⟨l, hl0, hl⟩ := h n hn
    rw [hl]
    simpa using hl0

end Frontier

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

