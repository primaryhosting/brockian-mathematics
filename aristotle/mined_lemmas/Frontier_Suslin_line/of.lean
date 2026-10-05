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

theorem of ZFC, and independence results cannot be established inside Lean's ambient set theory.
What *is* provable in ZFC, and is proved below, is the base case together with the reductions that
delimit the problem:

* separability implies the ccc, so a Suslin line is precisely a ccc linear continuum that fails the
  (a priori stronger) separability half of Cantor's characterisation;
* consequently no separable space — in particular neither `ℝ` nor `ℚ` — is a Suslin line;
* a Suslin line is uncountable and not second countable;
* being a Suslin line is invariant under order isomorphism, so no Suslin line is order isomorphic
  to `ℝ`;
* Suslin's Hypothesis is equivalent to: every ccc linear continuum is separable.
-/

/-- The **countable chain condition**: every family of pairwise disjoint nonempty open sets is
countable. -/
