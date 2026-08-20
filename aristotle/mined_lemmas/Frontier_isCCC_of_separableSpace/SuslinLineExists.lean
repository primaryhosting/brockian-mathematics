/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

def SuslinLineExists : Prop :=
  ∃ (X : Type) (i : LinearOrder X) (τ : TopologicalSpace X), @IsSuslinLine X i τ

/-- **Suslin's Hypothesis** (SH): there is no Suslin line.  Equivalently, every ccc densely
ordered linear order without endpoints (with its order topology) is separable.

SH is independent of ZFC: Jensen's diamond principle `◊` (which holds in Gödel's constructible
universe `L`) implies the existence of a Suslin line, hence `¬ SH`, while Martin's Axiom
together with `¬ CH` implies SH. -/
