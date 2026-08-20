/-
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 does not permit a module docstring to precede `import`, so the header above is
-- wrapped in an outer block comment.)
import Mathlib

open Finset Filter MeasureTheory
open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that the set `A ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with positive common difference `d`. -/

theorem exists_frequently_card_ge_of_pos_upperDensity (hA : 0 < upperDensity A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n ≥ N, 1 ≤ n ∧ ε * n ≤ #{x ∈ range n | x ∈ A} := by
  set f : ℕ → ℝ := fun n => (#{x ∈ range n | x ∈ A} : ℝ) / n with hf
  have hfnonneg : ∀ n : ℕ, 0 ≤ f n := fun n => by positivity
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop f := by
    refine ⟨0, fun a ha => ?_⟩
    obtain ⟨n, hn⟩ := (eventually_map.1 ha).exists
    exact (hfnonneg n).trans hn
  have hfreq : ∃ᶠ n in atTop, upperDensity A / 2 < f n :=
    frequently_lt_of_lt_limsup hcobdd (by simpa [upperDensity, hf] using half_lt_self hA)
  refine ⟨upperDensity A / 2, by positivity, fun N => ?_⟩
  obtain ⟨n, hn, hnN⟩ := (hfreq.and_eventually (eventually_ge_atTop (max N 1))).exists
  have hn1 : 1 ≤ n := le_of_max_le_right hnN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ⟨n, le_of_max_le_left hnN, hn1, by
    rw [hf] at hn
    exact (le_div_iff₀ hnpos).1 hn.le⟩

end Density

/-- Finitary Szemerédi is monotone in the length of the progression. -/
