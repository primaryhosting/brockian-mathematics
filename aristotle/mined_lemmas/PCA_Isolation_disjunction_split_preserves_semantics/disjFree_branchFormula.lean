import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## The isolation engine's model

An *isolation engine* for a proof-carrying app takes a constraint (a propositional
formula over abstract atoms, describing e.g. a capability guard) and splits it into
a list of independent, disjunction-free *branches*, each branch being a conjunction
of literals that can be discharged in isolation.

This file formalises that model and proves that the split is *semantics preserving*:
the disjunction of the produced branches is logically equivalent to the original
constraint (soundness: every satisfied branch entails the constraint; completeness:
every model of the constraint satisfies some branch).
-/

namespace PCA.Isolation

universe u
variable {α : Type u}

/-- Propositional constraints of the isolation engine. -/
inductive Formula (α : Type u) where
  | atom : α → Formula α
  | tru : Formula α
  | fls : Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α

/-- A literal: an atom, possibly negated. -/
structure Lit (α : Type u) where
  atom : α
  positive : Bool

/-- Semantics of constraints under a valuation `v` of the atoms. -/

theorem disjFree_branchFormula (c : List (Lit α)) : DisjFree (branchFormula c) := by
  induction c with
  | nil => trivial
  | cons l c ih =>
      refine ⟨?_, ih⟩
      unfold litFormula
      cases l.positive <;> trivial

/-- **Disjunction split preserves semantics.**

The isolation engine rewrites a constraint `f` into the disjunction of the
disjunction-free branches `split f`, and this rewriting is semantics preserving: for
every valuation of the atoms, the split constraint evaluates exactly as `f` does.
Moreover each branch is itself disjunction-free, so the branches can be discharged
in isolation. -/
