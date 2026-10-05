/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

/-- **Aggregation lemma (sure-thing principle).**

If the common-knowledge event `C` is partitioned into the information cells of an agent
(the cells are the fibres of `f` inside `C`, indexed by `I`), and on every cell the
conditional probability of `E` equals `q`, then the conditional probability of `E`
on all of `C` is again `q`.

Here `μ : Ω → ℝ` is the (common) prior weight function, the numerator
`∑ x ∈ S, if x ∈ E then μ x else 0` is the mass of `E ∩ S`, and the denominator
`∑ x ∈ S, μ x` is the mass of `S`; a statement `num = q * den` is the (denominator-free)
form of "the posterior of `E` given `S` is `q`". -/

theorem posterior_constant_on_cells
    {Ω ι : Type*} [DecidableEq ι]
    (μ : Ω → ℝ) (E C : Finset Ω) [DecidablePred (· ∈ E)]
    (f : Ω → ι) (I : Finset ι) (hf : ∀ x ∈ C, f x ∈ I) (q : ℝ)
    (h : ∀ i ∈ I, (∑ x ∈ C with f x = i, if x ∈ E then μ x else 0)
          = q * ∑ x ∈ C with f x = i, μ x) :
    (∑ x ∈ C, if x ∈ E then μ x else 0) = q * ∑ x ∈ C, μ x := by
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun x => if x ∈ E then μ x else 0),
      ← Finset.sum_fiberwise_of_maps_to hf μ, Finset.mul_sum]
  exact Finset.sum_congr rfl h

/-- **Aumann's agreement theorem (base case).**

Two agents share a common prior `μ` on a finite state space and consider an event `E`.
Let `C` be a common-knowledge event at the actual state: `C` is a union of cells of agent
1's information partition (the fibres of `f`, indexed by `I`) and also a union of cells of
agent 2's information partition (the fibres of `g`, indexed by `K`) — i.e. `C` is a member
of the meet of the two partitions.

Assume it is common knowledge that agent 1's posterior of `E` is `q₁` and agent 2's is `q₂`;
formally, on every cell of agent 1 inside `C` the posterior of `E` equals `q₁` (hypothesis
`h₁`, written in the denominator-free form `mass (E ∩ cell) = q₁ * mass cell`), and likewise
for agent 2 with `q₂`.

Then, provided `C` has positive prior mass, `q₁ = q₂`: the agents cannot agree to disagree. -/
