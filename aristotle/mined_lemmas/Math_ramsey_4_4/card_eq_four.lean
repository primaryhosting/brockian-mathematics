/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/

theorem card_eq_four {V : Type} [DecidableEq V] {s : Finset V} (hs : s.card = 4) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, s1, ha, rfl, hs1⟩ := Finset.card_eq_succ.mp hs
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hs1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, b, c, d, ha.1, ha.2.1, ha.2.2, hbc, hbd, hcd, rfl⟩

