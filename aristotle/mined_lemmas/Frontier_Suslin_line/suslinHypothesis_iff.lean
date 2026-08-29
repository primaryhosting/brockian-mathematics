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

theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (α : Type) [LinearOrder α] [TopologicalSpace α] [OrderTopology α],
        IsLinearContinuum α → IsCCC α → SeparableSpace α := by
  constructor
  · intro h α _ _ _ hcont hccc
    by_contra hsep
    exact h α ⟨hcont, hccc, hsep⟩
  · intro h α _ _ _ hsus
    exact hsus.not_separable (h α hsus.continuum hsus.ccc)

/-! ## The target statement -/

/-- **Suslin's problem.**  The formal statement of the problem together with the ZFC-provable base
case and reductions:

1. separability implies the countable chain condition, so a Suslin line is exactly a ccc linear
   continuum failing the separability clause of Cantor's characterisation of `ℝ`;
2. no separable space is a Suslin line; in particular neither `ℝ` nor `ℚ` is one;
3. a Suslin line is uncountable, not second countable, and not order isomorphic to `ℝ`;
4. Suslin's Hypothesis is exactly the assertion that every ccc linear continuum is separable.

(The independence of Suslin's Hypothesis from ZFC — `◊` yields a Suslin line, `MA + ¬CH` refutes
one — is not a ZFC theorem and hence is not asserted here.) -/
