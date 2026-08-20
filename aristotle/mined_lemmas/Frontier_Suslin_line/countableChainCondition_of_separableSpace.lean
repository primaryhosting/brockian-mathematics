import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

theorem countableChainCondition_of_separableSpace (X : Type u) [TopologicalSpace X]
    [SeparableSpace X] : CountableChainCondition X := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  intro S hopen hne hdisj
  -- choose a point of `D` in each member of `S`
  have hchoice : ∀ s : S, ∃ d, d ∈ D ∩ (s : Set X) := by
    rintro ⟨s, hs⟩
    have := hDd.inter_open_nonempty s (hopen s hs) (hne s hs)
    simpa [Set.inter_comm] using this
  choose f hf using hchoice
  have hinj : Function.Injective f := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    by_contra hne'
    have hst' : s ≠ t := by
      intro h; exact hne' (by cases h; rfl)
    have := hdisj hs ht hst'
    have h1 : f ⟨s, hs⟩ ∈ s := (hf ⟨s, hs⟩).2
    have h2 : f ⟨s, hs⟩ ∈ t := by rw [hst]; exact (hf ⟨t, ht⟩).2
    exact (Set.disjoint_left.mp this h1) h2
  have hDcount : Countable (↥D) := hDc.to_subtype
  have hginj : Function.Injective (fun s : S => (⟨f s, (hf s).1⟩ : ↥D)) := by
    intro s t hst
    exact hinj (congrArg Subtype.val hst)
  have hcount : Countable S := hginj.countable
  exact Set.countable_coe_iff.mp hcount

/-- A Suslin line is not separable, hence not countable. -/
