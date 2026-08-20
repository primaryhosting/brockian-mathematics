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

theorem TestSystem.pow_vars_mem (T : TestSystem) (n : ℕ) :
    ∀ c ∈ (T.pow n).tests, ∀ i ∈ c.vars, ∃ d ∈ T.tests, i ∈ d.vars := by
  induction n with
  | zero =>
      intro c hc i hi
      simp [TestSystem.pow] at hc
      subst hc
      simp [Constraint.triv] at hi
  | succ n ih =>
      intro c hc i hi
      have hc' : c ∈ T.tests.flatMap (fun c => (T.pow n).tests.map (fun d => c.conj d)) := hc
      rw [List.mem_flatMap] at hc'
      obtain ⟨d, hd, hmem⟩ := hc'
      rw [List.mem_map] at hmem
      obtain ⟨e, he, rfl⟩ := hmem
      simp only [Constraint.conj, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ⟨d, hd, hi⟩
      · exact ih e he i hi

/-! ## An abstract model of polynomial-time computation

Formalizing polynomial-time computability from scratch requires fixing a machine model.  We
instead work with an *abstract* model: a class `Ver` of polynomial-time computable verification
predicates and a class `Sys` of polynomial-time computable maps from inputs to test systems
(the tests being represented by their query tuples together with the truth tables of their
predicates), subject to the two closure properties that the arguments below need.  Both are
true of the standard notion of polynomial time, and everything is a hypothesis of the final
theorem: no new Lean axiom is introduced.
-/

/-- An abstract model of efficient (polynomial-time) computation. -/
structure EffModel where
  /-- `Ver V` says that the two-argument predicate `V` is polynomial-time computable. -/
  Ver : (Word → Word → Bool) → Prop
  /-- `Sys V` says that the map from an input to a test system is polynomial-time computable
  (tests being given by their query tuples and the truth tables of their predicates). -/
  Sys : (Word → TestSystem) → Prop
  /-- Given an efficiently computable test system, checking that *all* of its tests accept a
  candidate proof is a polynomial-time verification predicate. -/
  ver_all : ∀ {V : Word → TestSystem}, Sys V →
    Ver (fun x w => (V x).tests.all (fun c => c.sat (fun i => w.getD i false)))
  /-- For each fixed number `t` of repetitions, the `t`-fold repetition of an efficiently
  computable test system is efficiently computable. -/
  sys_pow : ∀ {V : Word → TestSystem} (t : ℕ), Sys V → Sys (fun x => (V x).pow t)
  /-- `Red f` says that the word function `f` is polynomial-time computable. -/
  Red : (Word → Word) → Prop
  /-- Efficient maps compose: precomposing an efficient test system with an efficient word
  function is efficient. -/
  sys_comp : ∀ {V : Word → TestSystem} {f : Word → Word}, Sys V → Red f →
    Sys (fun x => V (f x))
  /-- A polynomial-time computable word function has polynomially bounded output length. -/
  red_poly : ∀ {f : Word → Word}, Red f → ∃ k : ℕ, ∀ x : Word,
    (f x).length ≤ (x.length + 2) ^ k

/-! ## The classes NP and PCP(log n, 1) -/

/-- `NP`: languages with polynomial-length certificates checkable in polynomial time. -/
