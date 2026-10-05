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
def prob (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, p ω

/-- An agent's information structure is encoded by a labelling map `part : Ω → κ`:
the agent, at state `ω`, learns exactly the label `part ω`, i.e. the agent's
information cell at `ω` is the set of states carrying the same label. -/
def cell (part : Ω → κ) (ω : Ω) : Finset Ω := Finset.univ.filter (fun x => part x = part ω)

omit [DecidableEq Ω] in
lemma self_mem_cell (part : Ω → κ) (ω : Ω) : ω ∈ cell part ω := by
  simp [cell]

omit [DecidableEq Ω] in
lemma mem_cell_iff {part : Ω → κ} {ω x : Ω} : x ∈ cell part ω ↔ part x = part ω := by
  simp [cell]

/-- An event `C` is *closed* for the information structure `part` when knowing that the
true state lies in `C` is compatible with every state the agent cannot distinguish from
a state of `C`; equivalently, `C` is a union of information cells.  This is exactly the
condition defining events that the agent knows whenever they are true. -/
def IsClosed (part : Ω → κ) (C : Finset Ω) : Prop := ∀ ω ∈ C, cell part ω ⊆ C

/-- **Key lemma.**  If an event `C` is a union of an agent's information cells (i.e. it is
closed for that agent), and the agent's posterior probability of `E` equals `q` on every
cell meeting `C`, then the prior probability of `E ∩ C` is `q * prob C`: averaging the
constant posterior over the cells of `C` recovers the prior conditional probability. -/
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
theorem aumann_agreement (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (part₁ part₂ : Ω → κ) (E C : Finset Ω) (q₁ q₂ : ℝ) (ω₀ : Ω) (hω₀ : ω₀ ∈ C)
    (hC₁ : IsClosed part₁ C) (hC₂ : IsClosed part₂ C)
    (hcell₁ : ∀ ω ∈ C, 0 < prob p (cell part₁ ω))
    (hcell₂ : ∀ ω ∈ C, 0 < prob p (cell part₂ ω))
    (hpost₁ : ∀ ω ∈ C, prob p (cell part₁ ω ∩ E) / prob p (cell part₁ ω) = q₁)
    (hpost₂ : ∀ ω ∈ C, prob p (cell part₂ ω ∩ E) / prob p (cell part₂ ω) = q₂) :
    q₁ = q₂ := by
  classical
  -- The common-knowledge event `C` has positive prior probability.
  have hCpos : 0 < prob p C := by
    refine lt_of_lt_of_le (hcell₁ ω₀ hω₀) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (hC₁ ω₀ hω₀) (fun i _ _ => hp i)
  -- Turn the posterior hypotheses into product form.
  have hmul₁ : ∀ ω ∈ C, prob p (cell part₁ ω ∩ E) = q₁ * prob p (cell part₁ ω) := by
    intro ω hω
    have hne : prob p (cell part₁ ω) ≠ 0 := ne_of_gt (hcell₁ ω hω)
    rw [← hpost₁ ω hω]
    field_simp
  have hmul₂ : ∀ ω ∈ C, prob p (cell part₂ ω ∩ E) = q₂ * prob p (cell part₂ ω) := by
    intro ω hω
    have hne : prob p (cell part₂ ω) ≠ 0 := ne_of_gt (hcell₂ ω hω)
    rw [← hpost₂ ω hω]
    field_simp
  have h₁ := prob_inter_eq_of_posterior_const p part₁ E C q₁ hC₁ hmul₁
  have h₂ := prob_inter_eq_of_posterior_const p part₂ E C q₂ hC₂ hmul₂
  have : q₁ * prob p C = q₂ * prob p C := by rw [← h₁, ← h₂]
  exact mul_right_cancel₀ (ne_of_gt hCpos) this

/-- Sanity check (non-vacuity): the hypotheses of `Frontier.aumann_agreement` are
satisfiable.  Take `Ω = Bool` with the uniform prior, both agents completely uninformed,
the event `E = {true}`, and `C = Ω`; both posteriors equal `1/2`. -/
example :
    (∀ ω, (0:ℝ) ≤ (fun _ : Bool => (1:ℝ)/2) ω) ∧
    IsClosed (fun _ : Bool => ()) Finset.univ ∧
    (∀ ω ∈ (Finset.univ : Finset Bool), 0 < prob (fun _ => (1:ℝ)/2) (cell (fun _ => ()) ω)) ∧
    (∀ ω ∈ (Finset.univ : Finset Bool),
      prob (fun _ => (1:ℝ)/2) (cell (fun _ => ()) ω ∩ ({true} : Finset Bool)) /
        prob (fun _ => (1:ℝ)/2) (cell (fun _ => ()) ω) = 1/2) := by
  refine ⟨by norm_num, fun ω _ => Finset.subset_univ _, ?_, ?_⟩ <;>
    · intro ω _
      simp [prob, cell]

end Aumann

end Frontier

#print axioms Frontier.aumann_agreement

