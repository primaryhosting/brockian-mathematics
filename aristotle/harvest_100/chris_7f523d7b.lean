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
def cell [DecidableEq ι] (f : Ω → ι) (ω : Ω) : Finset Ω :=
  univ.filter (fun x => f x = f ω)

/-- If a set `M` of states is a union of information cells of the agent with signal `f`
(i.e. `M` is *self-evident* for that agent), and the agent's posterior probability of `E`
equals `q` on every cell contained in `M` (stated in the product form
`P (E ∩ C) = q * P C`), then `P (E ∩ M) = q * P M`. -/
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
theorem aumann_agreement [DecidableEq ι] [DecidableEq κ]
    (p : Ω → ℝ) (E : Finset Ω) (f : Ω → ι) (g : Ω → κ) (M : Finset Ω)
    (hMf : ∀ ω ∈ M, ∀ x, f x = f ω → x ∈ M)
    (hMg : ∀ ω ∈ M, ∀ x, g x = g ω → x ∈ M)
    (hMpos : 0 < ∑ x ∈ M, p x)
    (hfpos : ∀ ω ∈ M, 0 < ∑ x ∈ cell f ω, p x)
    (hgpos : ∀ ω ∈ M, 0 < ∑ x ∈ cell g ω, p x)
    (q₁ q₂ : ℝ)
    (hq₁ : ∀ ω ∈ M, (∑ x ∈ cell f ω, if x ∈ E then p x else 0)
             / (∑ x ∈ cell f ω, p x) = q₁)
    (hq₂ : ∀ ω ∈ M, (∑ x ∈ cell g ω, if x ∈ E then p x else 0)
             / (∑ x ∈ cell g ω, p x) = q₂) :
    q₁ = q₂ := by
  have h1 : ∑ x ∈ M, (if x ∈ E then p x else 0) = q₁ * ∑ x ∈ M, p x := by
    refine sum_over_self_evident_set p E f M hMf q₁ ?_
    intro ω hω
    rw [← hq₁ ω hω, div_mul_cancel₀ _ (hfpos ω hω).ne']
  have h2 : ∑ x ∈ M, (if x ∈ E then p x else 0) = q₂ * ∑ x ∈ M, p x := by
    refine sum_over_self_evident_set p E g M hMg q₂ ?_
    intro ω hω
    rw [← hq₂ ω hω, div_mul_cancel₀ _ (hgpos ω hω).ne']
  exact mul_right_cancel₀ hMpos.ne' (h1.symm.trans h2)

/-! ### A concrete instance, showing the hypotheses above are satisfiable non-trivially -/

/-- Agent 1's signal on the four-state space: it separates `{0,1}` from `{2,3}`. -/
def sig₁ : Fin 4 → ℕ := fun i => i.val / 2

/-- Agent 2's signal on the four-state space: it separates `{0,3}` from `{1,2}`. -/
def sig₂ : Fin 4 → ℕ := fun i => ((i.val + 1) / 2) % 2

lemma cell_sig₁ (ω : Fin 4) : cell sig₁ ω = if ω.val < 2 then {0, 1} else {2, 3} := by
  revert ω; decide

lemma cell_sig₂ (ω : Fin 4) :
    cell sig₂ ω = if ω.val = 0 ∨ ω.val = 3 then {0, 3} else {1, 2} := by
  revert ω; decide

/-- The two information partitions really are different (they are not refinements of
each other): states `0` and `1` are indistinguishable for agent 1 but distinguishable
for agent 2, and vice-versa for states `1` and `2`. -/
lemma sig_partitions_incomparable :
    sig₁ 0 = sig₁ 1 ∧ sig₂ 0 ≠ sig₂ 1 ∧ sig₂ 1 = sig₂ 2 ∧ sig₁ 1 ≠ sig₁ 2 := by
  decide

/-- All hypotheses of `aumann_agreement` are satisfiable: with the uniform prior on four
states, the event `E = {0, 2}`, the common knowledge event `M = univ`, and the two
different information partitions `sig₁`, `sig₂`, both agents' posteriors equal `1/2`
everywhere (and indeed the conclusion `q₁ = q₂` holds). -/
theorem aumann_agreement_instance :
    (0 < ∑ _x ∈ (univ : Finset (Fin 4)), (1:ℝ)/4) ∧
    (∀ ω : Fin 4, 0 < ∑ _x ∈ cell sig₁ ω, (1:ℝ)/4) ∧
    (∀ ω : Fin 4, 0 < ∑ _x ∈ cell sig₂ ω, (1:ℝ)/4) ∧
    (∀ ω : Fin 4, (∑ x ∈ cell sig₁ ω, if x ∈ ({0, 2} : Finset (Fin 4)) then (1:ℝ)/4 else 0)
        / (∑ _x ∈ cell sig₁ ω, (1:ℝ)/4) = 1/2) ∧
    (∀ ω : Fin 4, (∑ x ∈ cell sig₂ ω, if x ∈ ({0, 2} : Finset (Fin 4)) then (1:ℝ)/4 else 0)
        / (∑ _x ∈ cell sig₂ ω, (1:ℝ)/4) = 1/2) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₁]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₂]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₁]
  · intro ω; fin_cases ω <;> norm_num (config := { decide := true }) [cell_sig₂]

end Frontier

