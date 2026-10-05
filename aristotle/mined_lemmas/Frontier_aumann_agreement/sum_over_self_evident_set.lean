/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset

variable {Ω ι κ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell (element of the information partition) of an agent whose
information is described by the signal function `f`, at the state `ω`:
the set of states the agent cannot distinguish from `ω`. -/

lemma sum_over_self_evident_set [DecidableEq ι] (p : Ω → ℝ) (E : Finset Ω)
    (f : Ω → ι) (M : Finset Ω)
    (hM : ∀ ω ∈ M, ∀ x, f x = f ω → x ∈ M) (q : ℝ)
    (hq : ∀ ω ∈ M, ∑ x ∈ cell f ω, (if x ∈ E then p x else 0)
            = q * ∑ x ∈ cell f ω, p x) :
    ∑ x ∈ M, (if x ∈ E then p x else 0) = q * ∑ x ∈ M, p x := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := M.image f)
        (fun x hx => Finset.mem_image_of_mem f hx) (fun x => if x ∈ E then p x else 0),
      ← Finset.sum_fiberwise_of_maps_to (g := f) (t := M.image f)
        (fun x hx => Finset.mem_image_of_mem f hx) p,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b hb
  obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hb
  have hfib : M.filter (fun x => f x = f ω) = cell f ω := by
    ext x
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hM ω hω x h, h⟩⟩
  rw [hfib]
  exact hq ω hω

/-- **Aumann's agreement theorem** (finite case).

Two agents share a common prior `p` on a finite state space `Ω`, and their private
information is described by signal functions `f` and `g` (the information partitions
are the fibers of `f` and of `g`).  Let `M` be an event that is *common knowledge*:
it is a union of cells of each agent's partition (`hMf`, `hMg`).  If, throughout `M`,
agent 1's posterior probability of the event `E` is `q₁` and agent 2's posterior
probability of `E` is `q₂` — that is, the posteriors are common knowledge on `M` —
then `q₁ = q₂`: the agents cannot agree to disagree. -/
