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

variable {Ω κ κ' : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq κ] [DecidableEq κ']

/-- The (unnormalised) probability of a finite event `S`, for a weight function `w`. -/
def prob (w : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ x ∈ S, w x

/-- The information cell of an agent whose knowledge is described by the map `f`
(the agent, at state `x`, knows exactly the value `f x`): the set of states the agent
cannot distinguish from `x`. -/
def cell (f : Ω → κ) (x : Ω) : Finset Ω := Finset.univ.filter (fun y => f y = f x)

omit [DecidableEq Ω] in
lemma mem_cell {f : Ω → κ} {x y : Ω} : y ∈ cell f x ↔ f y = f x := by
  simp [cell]

/-- If `C` is a union of cells of the agent `f` (i.e. `C` is common knowledge for that agent)
and on every cell inside `C` the agent's posterior probability of `A` is `q`, then the
posterior probability of `A` given `C` is also `q`. -/
lemma prob_inter_of_posterior_const (w : Ω → ℝ) (A C : Finset Ω) (f : Ω → κ) (q : ℝ)
    (hck : ∀ x ∈ C, cell f x ⊆ C)
    (hpost : ∀ x ∈ C, prob w (A ∩ cell f x) = q * prob w (cell f x)) :
    prob w (A ∩ C) = q * prob w C := by
  classical
  -- the cells appearing inside `C`
  set T : Finset κ := C.image f with hT
  -- for `y ∈ T`, the fiber of `f` over `y` is a full cell contained in `C`
  have hfib : ∀ y ∈ T, ∃ x ∈ C, f x = y := by
    intro y hy
    simpa [hT, Finset.mem_image, eq_comm] using (Finset.mem_image.mp hy)
  -- decompose `C`
  have hC : prob w C = ∑ y ∈ T, prob w (C.filter (fun x => f x = y)) := by
    rw [prob]
    rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := T)
      (fun x hx => Finset.mem_image_of_mem f hx) w]
    rfl
  have hAC : prob w (A ∩ C) = ∑ y ∈ T, prob w ((A ∩ C).filter (fun x => f x = y)) := by
    rw [prob]
    rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := T)
      (fun x hx => Finset.mem_image_of_mem f (Finset.mem_of_mem_inter_right hx)) w]
    rfl
  have key : ∀ y ∈ T, prob w ((A ∩ C).filter (fun x => f x = y))
      = q * prob w (C.filter (fun x => f x = y)) := by
    intro y hy
    obtain ⟨x, hxC, hxy⟩ := hfib y hy
    subst hxy
    have hcellC : cell f x ⊆ C := hck x hxC
    have hc : C.filter (fun z => f z = f x) = cell f x := by
      ext z
      simp only [Finset.mem_filter, mem_cell]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨hcellC (mem_cell.mpr h), h⟩
    have hac : (A ∩ C).filter (fun z => f z = f x) = A ∩ cell f x := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_inter, mem_cell]
      constructor
      · rintro ⟨⟨hzA, -⟩, h⟩; exact ⟨hzA, h⟩
      · rintro ⟨hzA, h⟩; exact ⟨⟨hzA, hcellC (mem_cell.mpr h)⟩, h⟩
    rw [hc, hac]
    exact hpost x hxC
  rw [hAC, Finset.sum_congr rfl key, ← Finset.mul_sum, ← hC]

/-- **Aumann's agreement theorem** (finite, combinatorial form).

Two agents share a common prior given by the weights `w`.  Agent 1's information is described
by `f`, agent 2's by `g`.  `C` is an event of positive probability that is common knowledge:
it is a union of cells of each agent (`hfck`, `hgck`).  If, throughout `C`, agent 1's posterior
probability of the event `A` is `q₁` and agent 2's is `q₂` — so that the posteriors are common
knowledge — then `q₁ = q₂`: the agents cannot agree to disagree. -/
theorem aumann_agreement (w : Ω → ℝ) (A C : Finset Ω) (f : Ω → κ) (g : Ω → κ') (q₁ q₂ : ℝ)
    (hCpos : prob w C ≠ 0)
    (hfck : ∀ x ∈ C, cell f x ⊆ C) (hgck : ∀ x ∈ C, cell g x ⊆ C)
    (hf : ∀ x ∈ C, prob w (A ∩ cell f x) = q₁ * prob w (cell f x))
    (hg : ∀ x ∈ C, prob w (A ∩ cell g x) = q₂ * prob w (cell g x)) :
    q₁ = q₂ := by
  have h1 : prob w (A ∩ C) = q₁ * prob w C :=
    prob_inter_of_posterior_const w A C f q₁ hfck hf
  have h2 : prob w (A ∩ C) = q₂ * prob w C :=
    prob_inter_of_posterior_const w A C g q₂ hgck hg
  have : q₁ * prob w C = q₂ * prob w C := by rw [← h1, ← h2]
  exact mul_right_cancel₀ hCpos this

/-- Sanity check that the hypotheses of `aumann_agreement` are satisfiable non-vacuously:
four equiprobable states, two agents with genuinely different information partitions, both
assigning posterior probability `1/2` to the event `A` at every state. -/
example :
    ∃ (w : Fin 4 → ℝ) (A C : Finset (Fin 4)) (f g : Fin 4 → Bool) (q : ℝ),
      prob w C ≠ 0 ∧ (∀ x ∈ C, cell f x ⊆ C) ∧ (∀ x ∈ C, cell g x ⊆ C) ∧
      (∀ x ∈ C, prob w (A ∩ cell f x) = q * prob w (cell f x)) ∧
      (∀ x ∈ C, prob w (A ∩ cell g x) = q * prob w (cell g x)) ∧
      cell f 0 ≠ cell g 0 := by
  refine ⟨fun _ => 1, {0, 3}, Finset.univ, fun x => decide (x.val < 2),
    fun x => decide (x.val % 2 = 0), 1 / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prob]
  · intro x _; exact Finset.subset_univ _
  · intro x _; exact Finset.subset_univ _
  · intro x _
    fin_cases x <;>
      simp only [prob, cell, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_filter,
        Fin.sum_univ_four] <;> norm_num
  · intro x _
    fin_cases x <;>
      simp only [prob, cell, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_filter,
        Fin.sum_univ_four] <;> norm_num
  · decide

end Frontier

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

