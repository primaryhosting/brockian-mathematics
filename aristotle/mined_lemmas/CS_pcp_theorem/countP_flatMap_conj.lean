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

theorem countP_flatMap_conj (L M : List Constraint) (a : Assignment) :
    (L.flatMap (fun c => M.map (fun d => c.conj d))).countP (fun c => c.sat a)
      = (L.countP (fun c => c.sat a)) * (M.countP (fun c => c.sat a)) := by
  induction L with
  | nil => simp
  | cons c L ih =>
      rw [List.flatMap_cons, List.countP_append, ih, List.countP_map]
      by_cases hc : c.sat a = true
      · have : (fun c' => Constraint.sat c' a) ∘ (fun d => c.conj d)
            = fun d => d.sat a := by
          funext d; simp [hc]
        rw [this, List.countP_cons_of_pos (by simpa using hc)]
        ring
      · have hc' : c.sat a = false := by simpa using hc
        have : (fun c' => Constraint.sat c' a) ∘ (fun d => c.conj d)
            = fun _ => false := by
          funext d; simp [hc']
        rw [this, List.countP_cons_of_neg (by simp [hc'])]
        simp

