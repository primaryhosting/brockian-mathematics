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

section Aumann

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {κ : Type*} [DecidableEq κ]

/-- The prior probability of an event `S ⊆ Ω`, for a weight function `p : Ω → ℝ`. -/

theorem prob_inter_eq_of_posterior_const (p : Ω → ℝ) (part : Ω → κ) (E C : Finset Ω)
    (q : ℝ) (hC : IsClosed part C)
    (hpost : ∀ ω ∈ C, prob p (cell part ω ∩ E) = q * prob p (cell part ω)) :
    prob p (C ∩ E) = q * prob p C := by
  classical
  set t : Finset κ := C.image part
  have hmapsC : ∀ x ∈ C, part x ∈ t := fun x hx => Finset.mem_image_of_mem _ hx
  have hmapsCE : ∀ x ∈ C ∩ E, part x ∈ t := fun x hx =>
    Finset.mem_image_of_mem _ (Finset.mem_inter.mp hx).1
  have hfibC := Finset.sum_fiberwise_of_maps_to hmapsC p
  have hfibCE := Finset.sum_fiberwise_of_maps_to hmapsCE p
  have key : ∀ b ∈ t, (∑ x ∈ C ∩ E with part x = b, p x)
      = q * (∑ x ∈ C with part x = b, p x) := by
    intro b hb
    obtain ⟨w, hwC, rfl⟩ := Finset.mem_image.mp hb
    have h1 : (C.filter (fun x => part x = part w)) = cell part w := by
      ext x
      constructor
      · intro hx
        exact mem_cell_iff.mpr (Finset.mem_filter.mp hx).2
      · intro hx
        exact Finset.mem_filter.mpr ⟨hC w hwC hx, mem_cell_iff.mp hx⟩
    have h2 : ((C ∩ E).filter (fun x => part x = part w)) = cell part w ∩ E := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, mem_cell_iff]
      constructor
      · rintro ⟨⟨_, hxE⟩, hxb⟩; exact ⟨hxb, hxE⟩
      · rintro ⟨hxb, hxE⟩
        exact ⟨⟨hC w hwC (mem_cell_iff.mpr hxb), hxE⟩, hxb⟩
    have := hpost w hwC
    rw [prob, prob] at this
    calc (∑ x ∈ C ∩ E with part x = part w, p x)
        = ∑ x ∈ cell part w ∩ E, p x := by rw [h2]
      _ = q * ∑ x ∈ cell part w, p x := this
      _ = q * ∑ x ∈ C with part x = part w, p x := by rw [h1]
  calc prob p (C ∩ E) = ∑ b ∈ t, ∑ x ∈ C ∩ E with part x = b, p x := by
        rw [prob, hfibCE]
    _ = ∑ b ∈ t, q * ∑ x ∈ C with part x = b, p x := Finset.sum_congr rfl key
    _ = q * ∑ b ∈ t, ∑ x ∈ C with part x = b, p x := by rw [Finset.mul_sum]
    _ = q * prob p C := by rw [prob, hfibC]

/-- **Aumann's agreement theorem.**

Two agents share a common prior `p` on a finite state space `Ω`, and have information
structures `part₁`, `part₂` (each agent observes the label of the true state under its own
map, so its information cell at `ω` is `cell partᵢ ω`).

Let `C` be an event which is common knowledge whenever it obtains: it is closed for both
agents (`hC₁`, `hC₂`), i.e. it is a union of cells of each agent — this is precisely the
statement that `C` is a member of the *meet* of the two information partitions.  Suppose
that throughout `C` agent 1's posterior probability of the event `E` is `q₁` and agent 2's
posterior is `q₂`; that is, the posteriors `q₁` and `q₂` are common knowledge on `C`.

Then the agents cannot agree to disagree: `q₁ = q₂`.

Both posteriors equal the prior conditional probability `prob p (C ∩ E) / prob p C`, since
each is an average of the constant posterior over the agent's cells partitioning `C`. -/
