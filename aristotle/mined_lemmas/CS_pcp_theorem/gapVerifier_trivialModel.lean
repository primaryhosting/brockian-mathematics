/-
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Words, languages, proofs -/

/-- A binary word. -/
abbrev Word := List Bool

/-- A language: a set of binary words. -/
abbrev Lang := Word → Prop

/-- A PCP proof (proof oracle): an infinite binary string. -/
abbrev Assignment := ℕ → Bool

/-! ## Local tests (constraints)

A non-adaptive PCP verifier, on a fixed input `x` and a fixed random string, reads a fixed
tuple of positions of the proof oracle and applies a predicate to the bits it read.  Such a
single action is exactly a *constraint*.
-/

/-- A single local test: a list of queried proof positions together with a predicate on the
answers. -/
structure Constraint where
  /-- The positions of the proof oracle that are queried. -/
  vars : List ℕ
  /-- The acceptance predicate applied to the answers, in the order of `vars`. -/
  pred : List Bool → Bool

/-- The number of queries made by a test. -/

theorem gapVerifier_trivialModel (L : Lang) : GapVerifier trivialModel L := by
  classical
  refine ⟨fun x => if L x then ⟨[Constraint.triv], by simp⟩ else ⟨[Constraint.reject], by simp⟩,
    0, 0, 1 / 2, by norm_num, by norm_num, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    by_cases hx : L x <;> simp [hx, Constraint.arity, Constraint.triv, Constraint.reject] at ht ⊢
      <;> simp [ht]
  · intro x; by_cases hx : L x <;> simp [hx]
  · intro x t ht i hi
    by_cases hx : L x <;> simp [hx] at ht <;>
      simp [ht, Constraint.triv, Constraint.reject] at hi
  · intro x hx
    exact ⟨fun _ => false, by simp [hx, acceptProb, Constraint.sat, Constraint.triv]⟩
  · intro x hx a
    simp [hx, acceptProb, Constraint.sat, Constraint.reject]
    norm_num

