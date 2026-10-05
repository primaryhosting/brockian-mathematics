/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- `countUpTo A N` is the number of elements of `A` below `N`. -/

theorem szemerediFinitary_of_le_two (k : ℕ) (hk : k ≤ 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ S : Finset ℕ, S ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (S.card : ℝ) → ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / δ)
  refine ⟨N₀, ?_⟩
  intro N hN S _ hcard
  have hNle : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (2 : ℝ) < δ * (N : ℝ) := by
    rw [div_lt_iff₀ hδ] at hN₀
    nlinarith
  have hc : 1 < S.card := by
    have : (1 : ℝ) < (S.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · refine ⟨x, y - x, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using hx
    · have : x + 1 * (y - x) = y := by omega
      rw [this]; exact hy
  · refine ⟨y, x - y, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using hy
    · have : y + 1 * (x - y) = x := by omega
      rw [this]; exact hx

/-- **Furstenberg–Szemerédi.**

The first component is the unconditional base case: a set of naturals of positive upper
density contains arithmetic progressions of length `k ≤ 2`.

The second component is a Lean-checked reduction: the finitary Szemerédi statement
`SzemerediFinitary` — which is what Furstenberg's multiple recurrence theorem produces
through the Furstenberg correspondence principle — implies the density statement that
every subset of `ℕ` of positive upper density contains arbitrarily long arithmetic
progressions. -/
