/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Finset

/-- `A` has positive upper density: there is `δ > 0` such that infinitely many initial
segments `{0, …, n-1}` meet `A` in at least `δ * n` elements. -/

theorem szemerediFinitary_three : SzemerediFinitary 3 := by
  intro δ hδ
  refine ⟨cornersTheoremBound (δ / 3), fun n hn A hAn hAδ => ?_⟩
  have hnot : ¬ ThreeAPFree (A : Set ℕ) := roth_3ap_theorem_nat δ hδ hn A hAn hAδ
  rw [ThreeAPFree] at hnot
  push_neg at hnot
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hnot
  simp only [Finset.mem_coe] at ha hb hc
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hb
    · have : a + 2 * (b - a) = c := by omega
      rw [this]; exact hc
  · refine ⟨c, a - b, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hc
    · have : c + 1 * (a - b) = b := by omega
      rw [this]; exact hb
    · have : c + 2 * (a - b) = a := by omega
      rw [this]; exact ha

/-- Reduction of the infinitary statement to the finitary one: if the finitary Szemerédi
statement holds in length `k`, then every set of positive upper density contains a
`k`-term arithmetic progression. -/
