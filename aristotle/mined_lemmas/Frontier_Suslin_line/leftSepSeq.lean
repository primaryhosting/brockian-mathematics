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

noncomputable def leftSepSeq (Y : Type u) [TopologicalSpace Y] [Nonempty Y] :
    Ordinal.{u} → Y
  | a => if h : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) then
      h.choose else Classical.arbitrary Y
  termination_by a => a
  decreasing_by all_goals exact b.2

open Classical in
