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

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem cost_build {n : ℕ} : ∀ (l : List (Fin n)) (acc : Finset (Fin n)),
    (build l acc).cost = l.length + 1 := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih => intro acc; simp [build, cost, ih]

