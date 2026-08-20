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

theorem exists_repetitions (eps : ℚ) (heps : 0 < eps) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ p : ℚ, 0 ≤ p → p ≤ 1 - eps → p ^ t ≤ 1 / 2 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := (1 : ℚ) / 2) (y := 1 - eps)
    (by norm_num) (by linarith)
  refine ⟨n + 1, Nat.le_add_left 1 n, ?_⟩
  intro p hp hple
  have h0 : (0 : ℚ) ≤ 1 - eps := le_trans hp hple
  have hmono : p ^ (n + 1) ≤ (1 - eps) ^ (n + 1) := pow_le_pow_left₀ hp hple _
  have hshrink : (1 - eps) ^ (n + 1) ≤ (1 - eps) ^ n :=
    pow_le_pow_of_le_one h0 (by linarith) (Nat.le_succ n)
  linarith [hmono, hshrink, hn.le]

