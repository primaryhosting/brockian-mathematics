import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Finset

/-- The trace of a set `A ⊆ ℕ` on the initial segment `{0, 1, ..., N - 1}`. -/

theorem exists_threeAP_of_posUpperDensity {A : Set ℕ} (hA : HasPosUpperDensity A) :
    HasAPOfLength A 3 := by
  obtain ⟨δ, hδ, hdens⟩ := hA
  obtain ⟨N, hN, hcard⟩ := hdens (cornersTheoremBound (δ / 3))
  have hnot : ¬ ThreeAPFree ((trace A N : Finset ℕ) : Set ℕ) :=
    roth_3ap_theorem_nat δ hδ hN (trace A N) (trace_subset A N) hcard
  have hex : ∃ a ∈ trace A N, ∃ b ∈ trace A N, ∃ c ∈ trace A N, a + c = b + b ∧ a ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hnot fun a ha b hb c hc habc => hcon a ha b hb c hc habc
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := hex
  have haA : a ∈ A := mem_of_mem_trace ha
  have hbA : b ∈ A := mem_of_mem_trace hb
  have hcA : c ∈ A := mem_of_mem_trace hc
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using haA
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hbA
    · have : a + 2 * (b - a) = c := by omega
      rw [this]; exact hcA
  · refine ⟨c, a - b, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using hcA
    · have : c + 1 * (a - b) = b := by omega
      rw [this]; exact hbA
    · have : c + 2 * (a - b) = a := by omega
      rw [this]; exact haA

/-- **The reduction.**  The finitary form of Szemerédi's theorem implies the density form: any set
of natural numbers of positive upper density contains arithmetic progressions of every length. -/
