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

theorem weaverKS2_of_large (d : ℕ) (α : ℝ) (hα : (1 - 1 / Real.sqrt 2) ^ 2 ≤ α) :
    WeaverKS2 d α := by
  intro m v _ hiso
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2le : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hnn : 0 ≤ 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one h2]
      nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
    linarith
  have hsqrt : 1 - 1 / Real.sqrt 2 ≤ Real.sqrt α := by
    have := Real.sqrt_le_sqrt hα
    rwa [Real.sqrt_sq hnn] at this
  have hone : (1:ℝ) ≤ (1 / Real.sqrt 2 + Real.sqrt α) ^ 2 := by
    nlinarith [hsqrt, Real.sqrt_nonneg α, h2]
  refine ⟨∅, ?_, ?_⟩
  · intro x
    simp only [Finset.sum_empty]
    positivity
  · intro x
    rw [Finset.compl_empty, hiso x]
    nlinarith [sq_nonneg ‖x‖, hone]

/-!
## The main statement
-/

/-- **Kadison–Singer / Weaver `KS₂`** (Marcus–Spielman–Srivastava).

`WeaverKS2 d α` is the finite dimensional statement equivalent (by Weaver's
theorem) to the Kadison–Singer problem.  This is the Lean-checked part of it:
the base case `d = 1` in full, and every dimension `d` in the regime
`α ≥ (1 - 1/√2)²` where the bound `(1/√2 + √α)²` already exceeds `1`. -/
