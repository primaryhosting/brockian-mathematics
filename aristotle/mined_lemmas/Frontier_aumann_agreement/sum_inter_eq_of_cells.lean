import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section Aumann

variable {Ω : Type*} [DecidableEq Ω]

/-- If `I` assigns to each state its information cell (so that the cells form a partition of the
state space), `M` is a union of cells, and `g` sums to zero over every cell meeting `M`, then `g`
sums to zero over `M`. -/

theorem sum_inter_eq_of_cells (μ : Ω → ℝ) (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (hcell : ∀ x y, y ∈ I x → I y = I x)
    (E M : Finset Ω) (hclosed : ∀ x ∈ M, I x ⊆ M) (q : ℝ)
    (hq : ∀ x ∈ M, ∑ y ∈ I x ∩ E, μ y = q * ∑ y ∈ I x, μ y) :
    ∑ y ∈ M ∩ E, μ y = q * ∑ y ∈ M, μ y := by
  have key : ∀ S : Finset Ω,
      ∑ y ∈ S, ((if y ∈ E then μ y else 0) - q * μ y)
        = (∑ y ∈ S ∩ E, μ y) - q * ∑ y ∈ S, μ y := by
    intro S
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, ← Finset.mul_sum]
  have h := sum_eq_zero_of_cells I hself hcell
    (fun y => (if y ∈ E then μ y else 0) - q * μ y) M hclosed
    (fun x hx => by rw [key]; rw [hq x hx]; ring)
  rw [key] at h
  linarith

/-- **Aumann's agreement theorem** (finite, base case).

Two agents share a common prior `μ` on a finite state space `Ω`.  Agent `i`'s information is
described by the partition `I i` (`I i ω` is the cell of agent `i` containing `ω`).  The event `M`
is *common knowledge* at the true state `ω₀`: it contains `ω₀` and is a union of cells of both
agents.  If, throughout `M`, agent `1`'s posterior probability of the event `E` is `q₁` and agent
`2`'s posterior probability of `E` is `q₂` (this is the content of "the posteriors are common
knowledge"), then `q₁ = q₂`: the agents cannot agree to disagree.

Posteriors are expressed in the multiplicative form `μ (C ∩ E) = q * μ C`, which is equivalent to
`μ (C ∩ E) / μ C = q` on cells of positive probability and avoids division by zero elsewhere. -/
