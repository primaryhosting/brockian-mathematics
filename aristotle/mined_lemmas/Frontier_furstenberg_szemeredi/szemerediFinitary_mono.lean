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

theorem szemerediFinitary_mono {j k : ℕ} (hjk : j ≤ k) (hk : SzemerediFinitary k) :
    SzemerediFinitary j := by
  intro ε hε
  obtain ⟨N, hN⟩ := hk ε hε
  refine ⟨N, fun n hn A hA hcard => ?_⟩
  obtain ⟨a, d, hd, h⟩ := hN n hn A hA hcard
  exact ⟨a, d, hd, fun i hi => h i (hi.trans_le hjk)⟩

/-- **Roth's theorem** gives the finitary Szemerédi statement for progressions of length `3`. -/
