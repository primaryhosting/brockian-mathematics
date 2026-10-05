/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` lines to precede every command, and a `/-! ... -/` module
-- docstring counts as a command; the mandated header is therefore reproduced verbatim above
-- as an ordinary block comment.
import Archive.Wiedijk100Theorems.FriendshipGraphs

namespace Frontier

open scoped Classical

/-- **The Friendship Theorem** (Erdős–Rényi–Sós).

In a finite, nonempty population with a symmetric, irreflexive friendship relation, if every
two distinct people have exactly one common friend, then someone is a friend of everybody
else. -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V]
    (friend : V → V → Prop) (hsymm : Symmetric friend) (hirr : ∀ v, ¬ friend v v)
    (hone : ∀ v w : V, v ≠ w → ∃! u : V, friend v u ∧ friend w u) :
    ∃ p : V, ∀ q : V, q ≠ p → friend p q := by
  set G : SimpleGraph V := ⟨friend, hsymm, ⟨hirr⟩⟩
  have hfr : Theorems100.Friendship G := by
    intro v w hvw
    obtain ⟨u, hu, huniq⟩ := hone v w hvw
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨u, ?_⟩, ?_⟩
    · exact (SimpleGraph.mem_commonNeighbors G).mpr hu
    · rintro ⟨y, hy⟩
      exact Subtype.ext (huniq y ((SimpleGraph.mem_commonNeighbors G).mp hy))
  obtain ⟨p, hp⟩ := Theorems100.friendship_theorem hfr
  exact ⟨p, fun q hq => hp q (Ne.symm hq)⟩

end Frontier

-- Axiom check: only the standard Lean/Mathlib axioms are used.
#print axioms Frontier.friendship_theorem

import Mathlib

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

