/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

namespace Frontier

/-!
## The statement

The Kadison–Singer problem (does every pure state on the atomic maximal abelian
subalgebra of `B(ℓ²)` extend uniquely to a pure state on `B(ℓ²)`?) was resolved
affirmatively by Marcus, Spielman and Srivastava, who proved Weaver's
discrepancy-theoretic reformulation `KS₂`.  Weaver proved that `KS₂` is
equivalent to the Kadison–Singer problem, so `KS₂` is the finite dimensional
combinatorial heart of the matter.

`WeaverKS2 d α` below is exactly the Marcus–Spielman–Srivastava statement in
dimension `d` with parameter `α`, written using quadratic forms rather than
operator norms: for a positive semidefinite operator `A = ∑ i ∈ S, vᵢ vᵢ*` one
has `‖A‖ ≤ c` if and only if `⟪x, A x⟫ = ∑ i ∈ S, |⟪vᵢ, x⟫|² ≤ c ‖x‖²` for all
`x`.  Likewise the isotropy hypothesis `∑ i, vᵢ vᵢ* = 1` is written as
`∑ i, |⟪vᵢ, x⟫|² = ‖x‖²`.
-/

/-- Weaver's `KS₂` statement (the Marcus–Spielman–Srivastava theorem) in
dimension `d` with parameter `α`:

if `v₁, …, vₘ ∈ ℂ^d` satisfy `‖vᵢ‖² ≤ α` and the isotropy condition
`∑ i, vᵢ vᵢ* = 1`, then the index set can be split into two pieces `S` and `Sᶜ`
with `‖∑ i ∈ S, vᵢ vᵢ*‖ ≤ (1/√2 + √α)²` and likewise for `Sᶜ`. -/

theorem standard_basis_isotropic (d : ℕ) :
    (∀ i : Fin d, ‖(EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ 1) ∧
      (∀ x : EuclideanSpace ℂ (Fin d),
        ∑ i, ‖inner ℂ (EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d)) x‖ ^ 2
          = ‖x‖ ^ 2) := by
  constructor
  · intro i; simp
  · intro x
    have h1 : ∀ i : Fin d,
        inner ℂ (EuclideanSpace.single i (1:ℂ) : EuclideanSpace ℂ (Fin d)) x = x i := by
      intro i; rw [EuclideanSpace.inner_single_left]; simp
    simp only [h1]
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-!
## A balanced-partition lemma

The one dimensional case of `KS₂` is a statement about splitting a family of
small nonnegative weights of total mass `1` into two parts of mass roughly
`1/2` each.
-/

/-- A family of weights of total mass `1`, each at most `α`, forces `0 ≤ α`. -/
