/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set TopologicalSpace

namespace Frontier

/-!
# Suslin's Problem

A *Suslin line* is a linear order, carrying its order topology, which satisfies the
**countable chain condition** (every family of pairwise disjoint nonempty open sets is
countable) but which is **not separable**.  Since every separable space is ccc
(`Frontier.isCCC_of_separableSpace`), a Suslin line is a space where the ccc fails to
imply separability.

*Suslin's Problem* asks whether every nonempty, ccc, densely ordered, unbounded,
conditionally complete linear order is order-isomorphic to `ℝ`; *Suslin's Hypothesis* is
the assertion that no Suslin line exists.

Both are independent of ZFC: Jensen's diamond principle `◊` implies that a Suslin line
exists, whereas `MA + ¬CH` implies Suslin's Hypothesis.  Consequently neither the
existence nor the nonexistence of a Suslin line is a theorem of ZFC, so neither can be
proved (nor refuted) in Lean's ambient set theory; the independence statements themselves
are assertions about models of ZFC rather than statements in the ZFC-like foundation Lean
formalises.

What *is* a theorem of ZFC, and is proved here, is the precise reduction of Suslin's
Problem to the nonexistence of a *Suslin continuum* (`Frontier.Suslin_line`), whose
mathematical core is Cantor's characterisation of the real line
(`Frontier.nonempty_orderIso_real`): a nonempty separable densely ordered unbounded
conditionally complete linear order is order-isomorphic to `ℝ`.  In particular Suslin's
Hypothesis implies the positive answer to Suslin's Problem, and conversely a positive
answer rules out all *complete* Suslin lines.

Mathlib has no notion of the countable chain condition, no notion of Suslin line, and no
characterisation of `ℝ` as an ordered topological space, so all of this is developed from
scratch here; the Mathlib inputs used are Cantor's isomorphism theorem for countable dense
linear orders (`Order.iso_of_countable_dense`), `exists_countable_dense`, and
`OrderIso.toHomeomorph`.
-/

/-- The **countable chain condition**: every family of pairwise disjoint nonempty open
sets is countable. -/

theorem not_suslinHypothesis_of_isSuslinContinuum (X : Type)
    [inst1 : ConditionallyCompleteLinearOrder X] [inst2 : TopologicalSpace X]
    (hX : IsSuslinContinuum X) : ¬ SuslinHypothesis := by
  obtain ⟨hot, -, -, -, -, hccc, hnsep⟩ := hX
  exact fun hSH => hSH X inst1.toLinearOrder inst2 ⟨hot, hccc, hnsep⟩

/-!
## Main theorem
-/

/-- **Suslin's Problem.**  The positive answer to Suslin's Problem — every nonempty ccc
densely ordered unbounded conditionally complete linear order, with its order topology, is
order-isomorphic to `ℝ` — holds if and only if there is no Suslin continuum, i.e. no such
order which fails to be separable.  Moreover Suslin's Hypothesis (there is no Suslin line
at all) implies the positive answer.

This is a theorem of ZFC; whether either side holds is *not* decided by ZFC: Jensen's `◊`
yields a Suslin line, whereas `MA + ¬CH` refutes all of them. -/
