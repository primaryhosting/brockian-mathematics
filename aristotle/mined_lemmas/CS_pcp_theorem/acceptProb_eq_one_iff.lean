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

theorem acceptProb_eq_one_iff (T : TestSystem) (a : Assignment) :
    acceptProb T a = 1 ↔ ∀ c ∈ T.tests, c.sat a = true := by
  have hlen : (0 : ℚ) < (T.tests.length : ℚ) := by exact_mod_cast T.length_pos
  rw [acceptProb, div_eq_one_iff_eq (ne_of_gt hlen)]
  constructor
  · intro h
    have : T.tests.countP (fun c => c.sat a) = T.tests.length := by exact_mod_cast h
    have := (List.countP_eq_length (l := T.tests) (p := fun c => c.sat a)).mp this
    simpa using this
  · intro h
    have : T.tests.countP (fun c => c.sat a) = T.tests.length :=
      (List.countP_eq_length (l := T.tests) (p := fun c => c.sat a)).mpr (by simpa using h)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) this

/-! ## Sequential repetition of a test system -/

/-- Independent `n`-fold repetition of a test system: perform `n` independent runs of the
verifier and accept iff all of them accept. -/
