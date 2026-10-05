/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem RamF.of_compl {G : SimpleGraph V} {T : Finset V} {p q : ℕ}
    (h : RamF Gᶜ T p q) : RamF G T q p := by
  rcases h with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
  · exact Or.inr ⟨s, hs, hc⟩
  · rw [compl_compl] at hc; exact Or.inl ⟨s, hs, hc⟩

omit [LinearOrder V] in
