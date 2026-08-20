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

theorem szemerediFinitary_three : SzemerediFinitary 3 := by
  have key : ∀ (A : Finset ℕ) (x y z : ℕ), x ∈ A → y ∈ A → z ∈ A → x < y → y < z →
      x + z = y + y → ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ A := by
    intro A x y z hx hy hz hxy hyz hsum
    refine ⟨x, y - x, by omega, fun i hi => ?_⟩
    interval_cases i
    · simpa using hx
    · have : x + 1 * (y - x) = y := by omega
      rw [this]; exact hy
    · have : x + 2 * (y - x) = z := by omega
      rw [this]; exact hz
  intro ε hε
  refine ⟨cornersTheoremBound (ε / 3), fun n hn A hA hcard => ?_⟩
  by_contra hcon
  refine roth_3ap_theorem_nat ε hε hn A hA hcard ?_
  intro a ha b hb c hc habc
  by_contra hab
  simp only [mem_coe] at ha hb hc
  rcases lt_or_gt_of_ne hab with h | h
  · exact hcon (key A a b c ha hb hc h (by omega) habc)
  · exact hcon (key A c b a hc hb ha (by omega) h (by omega))

/-- Unconditional finitary Szemerédi for progressions of length at most `3`. -/
