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

import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# The Friendship Theorem (Erdős–Rényi–Sós)

If, in a finite nonempty population, every two distinct people have exactly one common
friend, then some person is a friend of everyone else.

The statement here is phrased directly in terms of a friendship relation
(symmetric and irreflexive) rather than in terms of `SimpleGraph`; the proof
translates it into the graph-theoretic formulation and appeals to the development
of the friendship theorem in `Archive.Wiedijk100Theorems.FriendshipGraphs`
(Aaron Anderson, Jalex Stark, Kyle Miller).
-/

namespace Frontier

/-- A finite set (of cardinality-one type) criterion: a set has exactly one element
iff there is a unique element of it. -/

theorem card_eq_one_iff_existsUnique {α : Type*} (s : Set α) [Fintype s] :
    Fintype.card s = 1 ↔ ∃! x, x ∈ s := by
  rw [Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    exact ⟨x, hx, fun y hy => congrArg Subtype.val (h ⟨y, hy⟩)⟩
  · rintro ⟨x, hx, hu⟩
    exact ⟨⟨x, hx⟩, fun ⟨y, hy⟩ => Subtype.ext (hu y hy)⟩

/-- **The friendship theorem** (Erdős, Rényi, Sós).

In a finite nonempty population with a symmetric, irreflexive friendship relation,
if every two distinct people have exactly one common friend, then there is a person
who is a friend of everybody else. -/
