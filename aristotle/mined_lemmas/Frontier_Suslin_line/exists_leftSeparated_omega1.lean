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

theorem exists_leftSeparated_omega1 (Y : Type u) [TopologicalSpace Y] [Nonempty Y]
    (hns : ¬ SeparableSpace Y) :
    ∃ f : Ordinal.{u} → Y,
      (∀ a < (Cardinal.aleph 1).ord, f a ∉ closure (f '' Set.Iio a)) ∧
        Set.InjOn f (Set.Iio (Cardinal.aleph 1).ord) := by
  refine ⟨leftSepSeq Y, fun a ha => leftSepSeq_notMem_closure Y hns ha, ?_⟩
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact leftSepSeq_notMem_closure Y hns hb
      (subset_closure ⟨a, h, hab⟩)
  · exact leftSepSeq_notMem_closure Y hns ha
      (subset_closure ⟨b, h, hab.symm⟩)

/-- A Suslin line carries a left-separated `ω₁`-sequence. -/
