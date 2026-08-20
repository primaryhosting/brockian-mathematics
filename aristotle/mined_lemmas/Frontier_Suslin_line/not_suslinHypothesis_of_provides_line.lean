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

theorem not_suslinHypothesis_of_provides_line (P : Prop) (hP : P)
    (h : P → ∃ (X : Type) (lo : LinearOrder X) (t : TopologicalSpace X),
      ∃ _ : @OrderTopology X t _, @IsSuslinLine X lo t ‹_›) :
    ¬ SuslinHypothesis := by
  obtain ⟨X, lo, t, ot, hS⟩ := h hP
  intro hSH
  exact hSH X hS

/-! ## Main statement -/

/-- **Suslin's problem, formalized.**  We record:
1. every separable space is ccc (so a Suslin line is precisely a ccc, non-separable linear order);
2. Suslin's Hypothesis is equivalent to "every ccc LOTS is separable";
3. its negation is precisely the existence of a Suslin line;
4. the real line is not a Suslin line, and every Suslin line is uncountable and not second
   countable;
5. the base step of the reduction of a Suslin line to a Suslin tree: in a dense Suslin line every
   countable set misses a nonempty open interval;
6. the transfinite form of that step: every Suslin line carries an injective, left-separated
   `ω₁`-sequence. -/
