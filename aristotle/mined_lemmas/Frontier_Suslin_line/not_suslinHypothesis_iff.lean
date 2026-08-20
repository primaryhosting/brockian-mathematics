import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/

theorem not_suslinHypothesis_iff :
    ¬ SuslinHypothesis ↔
      ∃ (X : Type) (_ : LinearOrder X) (t : TopologicalSpace X),
        ∃ _ : @OrderTopology X t _, @IsCCC X t ∧ ¬ @SeparableSpace X t := by
  constructor
  · intro h
    by_contra hex
    apply h
    intro X _ _ _ hS
    exact hex ⟨X, ‹_›, ‹_›, ‹_›, hS.1, hS.2⟩
  · rintro ⟨X, lo, t, ot, hccc, hsep⟩ h
    exact @h X lo t ot ⟨hccc, hsep⟩

/-- **Reduction schema for `◊`-type hypotheses.**  Any principle `P` which produces a ccc
non-separable linearly ordered topological space refutes Suslin's Hypothesis; conversely any
principle implied by `SH` is consistent with `SH`.  This is the shape of Jensen's theorem
`◊ → ¬ SH`. -/
