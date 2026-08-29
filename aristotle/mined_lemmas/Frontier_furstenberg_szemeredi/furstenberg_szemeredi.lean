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

theorem furstenberg_szemeredi :
    (∀ A : Set ℕ, 0 < upperDensity A → ∀ k ≤ 2, HasAP A k) ∧
    (SzemerediFinitary → ∀ A : Set ℕ, 0 < upperDensity A → ∀ k : ℕ, HasAP A k) := by
  constructor
  · -- base case `k ≤ 2`
    intro A hA k hk
    have hinf := infinite_of_upperDensity_pos A hA
    obtain ⟨a, ha⟩ := hinf.nonempty
    have : ((A \ {n : ℕ | n ≤ a}) : Set ℕ).Nonempty := by
      have : ((A \ {n : ℕ | n ≤ a}) : Set ℕ).Infinite :=
        hinf.diff (Set.Finite.subset (Set.finite_Iic a) (by intro x hx; exact hx))
      exact this.nonempty
    obtain ⟨b, hb, hba⟩ := this
    simp only [Set.mem_setOf_eq, not_le] at hba
    refine ⟨a, b - a, by omega, ?_⟩
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi hk
    interval_cases i
    · simpa using ha
    · have : a + 1 * (b - a) = b := by omega
      rw [this]; exact hb
  · -- reduction from the finitary statement
    intro hSz A hA k
    obtain ⟨δ, hδ, hwin⟩ := exists_density_windows A hA
    obtain ⟨N₀, hN₀⟩ := hSz k δ hδ
    obtain ⟨N, hNM, hN⟩ := hwin N₀
    obtain ⟨a, d, hd, hmem⟩ :=
      hN₀ N hNM ((Finset.range N).filter (fun n => n ∈ A)) (Finset.filter_subset _ _)
        (by simpa [countUpTo] using hN)
    exact ⟨a, d, hd, fun i hi => (Finset.mem_filter.mp (hmem i hi)).2⟩

end Frontier

