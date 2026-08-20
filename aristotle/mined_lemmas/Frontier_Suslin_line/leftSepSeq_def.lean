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

theorem leftSepSeq_def (Y : Type u) [TopologicalSpace Y] [Nonempty Y] (a : Ordinal.{u}) :
    leftSepSeq Y a =
      if h : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) then
        h.choose else Classical.arbitrary Y := by
  rw [leftSepSeq]

/-- Initial segments of `ω₁` are countable. -/
