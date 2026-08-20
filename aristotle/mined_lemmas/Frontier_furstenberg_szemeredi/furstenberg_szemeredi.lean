/- (Lean requires `import` to precede any module docstring, so the header below is a
plain block comment; it is repeated verbatim as a module docstring after the import.)
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

open Filter Finset

namespace Frontier

noncomputable section

open Classical in
/-- The number of elements of `A` below `N`. -/

theorem furstenberg_szemeredi (k : ℕ) (hfin : FinitarySzemeredi k)
    (A : Set ℕ) (hA : HasPositiveUpperDensity A) : HasAP A k := by
  classical
  obtain ⟨δ, hδ, hδA⟩ := hA
  obtain ⟨N₀, hN₀⟩ := hfin δ hδ
  obtain ⟨N, hN, hcount⟩ := hδA N₀
  set S : Finset ℕ := (Finset.range N).filter (fun n => n ∈ A) with hS
  have hmem : ∀ n ∈ S, n < N := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1
  have hcard : δ * N ≤ (S.card : ℝ) := by
    simpa [hS, countBelow] using hcount
  obtain ⟨a, d, hd, h⟩ := hN₀ N hN S hmem hcard
  refine ⟨a, d, hd, fun i hi => ?_⟩
  have := h i hi
  rw [hS, Finset.mem_filter] at this
  exact this.2

