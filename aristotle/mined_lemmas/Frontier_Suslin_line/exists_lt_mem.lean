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

theorem exists_lt_mem (hs : Dense s) (x : X) : ∃ d : s, x < (d : X) := by
  obtain ⟨y, hy⟩ := exists_gt x
  obtain ⟨z, hz, hz1, _⟩ := hs.exists_between hy
  exact ⟨⟨z, hz⟩, hz1⟩

omit [NoMinOrder X] [NoMaxOrder X] [Nonempty X] in
