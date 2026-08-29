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

theorem isLinearContinuum_of_orderIso {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (h : IsLinearContinuum α) : IsLinearContinuum β := by
  obtain ⟨hne, hd, hmin, hmax, hlub⟩ := h
  refine ⟨hne.map e, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · intro a b hab
    obtain ⟨c, hc1, hc2⟩ := hd.dense (e.symm a) (e.symm b) (e.symm.lt_iff_lt.2 hab)
    exact ⟨e c, by simpa using e.lt_iff_lt.2 hc1, by simpa using e.lt_iff_lt.2 hc2⟩
  · intro a
    obtain ⟨b, hb⟩ := hmin.exists_lt (e.symm a)
    exact ⟨e b, by simpa using e.lt_iff_lt.2 hb⟩
  · intro a
    obtain ⟨b, hb⟩ := hmax.exists_gt (e.symm a)
    exact ⟨e b, by simpa using e.lt_iff_lt.2 hb⟩
  · intro s hs hbdd
    obtain ⟨y, hy⟩ := hs
    obtain ⟨x, hx⟩ := hlub (e ⁻¹' s) ⟨e.symm y, by simpa using hy⟩
      ((OrderIso.bddAbove_preimage e).2 hbdd)
    refine ⟨e x, ?_⟩
    have := (OrderIso.isLUB_image' e).2 hx
    rwa [Set.image_preimage_eq _ e.surjective] at this

/-- Being a Suslin line is invariant under order isomorphism (an order isomorphism between spaces
carrying the order topology is a homeomorphism). -/
