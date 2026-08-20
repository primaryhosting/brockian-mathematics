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

theorem finitarySzemeredi_mono {k l : ℕ} (hkl : k ≤ l) (h : FinitarySzemeredi l) :
    FinitarySzemeredi k := by
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := h δ hδ
  refine ⟨N₀, fun N hN S hS hcard => ?_⟩
  obtain ⟨a, d, hd, hap⟩ := hN₀ N hN S hS hcard
  exact ⟨a, d, hd, fun i hi => hap i (lt_of_lt_of_le hi hkl)⟩

/-- Unconditional base cases: a set of positive upper density contains arithmetic
progressions of length `k` for every `k ≤ 2`. -/
