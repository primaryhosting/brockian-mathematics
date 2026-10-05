/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the same header is repeated as the module
-- docstring immediately below the import.)
import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-!
## Suslin's problem, stated precisely

A *linear continuum* is a nonempty densely ordered linear order without endpoints in which every
nonempty bounded-above set has a least upper bound (i.e. `ℝ`-like order completeness).

The *countable chain condition* (ccc) says: every family of pairwise disjoint nonempty open sets is
countable.

A **Suslin line** is a linear continuum, equipped with its order topology, which satisfies the ccc
but is *not* separable.  Cantor's theorem characterises `ℝ` as the unique separable linear
continuum; **Suslin's problem** asks whether "separable" may be weakened to "ccc" in that
characterisation, i.e. whether a Suslin line exists.  The statement "no Suslin line exists" is
*Suslin's Hypothesis* (`Frontier.SuslinHypothesis` below).

Suslin's Hypothesis is independent of ZFC (Jech, Tennenbaum, Solovay–Tennenbaum): Jensen's diamond
principle `◊` implies that a Suslin line exists, while `MA + ¬CH` implies that none does.  Neither
implication — nor any "iff" between the existence of a Suslin line and `◊`-type hypotheses — is a

theorem isCCC_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (h : IsCCC α) : IsCCC β := by
  intro S hopen hne hdisj
  have hcount : ((fun s => e ⁻¹' s) '' S).Countable := by
    refine h _ ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (hopen s hs).preimage e.continuous
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨x, hx⟩ := hne s hs
      exact ⟨e.symm x, by simpa using hx⟩
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      have hst' : s ≠ t := by rintro rfl; exact hst rfl
      have hdis := hdisj hs ht hst'
      simp only [id_eq, Set.disjoint_left] at hdis ⊢
      intro x hx hx'
      exact hdis hx hx'
  have hS : S = (fun s => e '' s) '' ((fun s => e ⁻¹' s) '' S) := by
    ext s
    constructor
    · intro hs
      exact ⟨e ⁻¹' s, ⟨s, hs, rfl⟩, by simp [Set.image_preimage_eq _ e.surjective]⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      simpa [Set.image_preimage_eq _ e.surjective] using ht
  rw [hS]
  exact hcount.image _

