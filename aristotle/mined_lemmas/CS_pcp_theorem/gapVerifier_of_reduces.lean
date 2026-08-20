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

theorem gapVerifier_of_reduces (M : EffModel) (L K : Lang) (hred : Reduces M L K)
    (hK : GapVerifier M K) : GapVerifier M L := by
  obtain ⟨f, hf, hfL⟩ := hred
  obtain ⟨k, hk⟩ := M.red_poly hf
  obtain ⟨V, q, c, eps, heps, heps1, hSys, hq, hlen, hvars, hcomp, hsound⟩ := hK
  refine ⟨fun x => V (f x), q, (k + 2) * c, eps, heps, heps1, M.sys_comp hSys hf, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x t ht; exact hq (f x) t ht
  · intro x
    calc (V (f x)).tests.length ≤ ((f x).length + 2) ^ c := hlen (f x)
      _ ≤ ((x.length + 2) ^ k + 2) ^ c := Nat.pow_le_pow_left (by have := hk x; omega) c
      _ ≤ (x.length + 2) ^ ((k + 2) * c) := poly_comp_bound _ _ _
  · intro x t ht i hi
    have h1 : i < ((f x).length + 2) ^ c := hvars (f x) t ht i hi
    have h2 : ((f x).length + 2) ^ c ≤ ((x.length + 2) ^ k + 2) ^ c :=
      Nat.pow_le_pow_left (by have := hk x; omega) c
    have h3 := poly_comp_bound x.length k c
    omega
  · intro x hx; exact hcomp (f x) ((hfL x).mp hx)
  · intro x hx a; exact hsound (f x) (fun h => hx ((hfL x).mpr h)) a

/-- A constant-gap PCP for a single NP-hard language gives constant-gap PCPs for all of NP. -/
