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

theorem exists_leftSeparated_omega1_of_isSuslinLine {Y : Type u} [LinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] (h : IsSuslinLine Y) :
    ∃ f : Ordinal.{u} → Y,
      (∀ a < (Cardinal.aleph 1).ord, f a ∉ closure (f '' Set.Iio a)) ∧
        Set.InjOn f (Set.Iio (Cardinal.aleph 1).ord) := by
  haveI : Uncountable Y := uncountable_of_isSuslinLine h
  haveI : Nonempty Y := inferInstance
  exact exists_leftSeparated_omega1 Y h.2

/-! ## Precise form of Suslin's problem -/

/-- Suslin's Hypothesis says exactly that every ccc linearly ordered topological space is
separable. -/
