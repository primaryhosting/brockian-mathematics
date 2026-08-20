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

/-- The posterior probability that an agent with information partition `cell`
assigns to the event `E` at the state `ω`, under the prior weights `p`:
it is `p (E ∩ cell ω) / p (cell ω)`. -/

theorem aumann_agreement {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (E : Finset Ω) (c₁ c₂ : Ω → Finset Ω)
    (hself₁ : ∀ ω, ω ∈ c₁ ω) (hpart₁ : ∀ ω ω', ω' ∈ c₁ ω → c₁ ω' = c₁ ω)
    (hpos₁ : ∀ ω, 0 < ∑ x ∈ c₁ ω, p x)
    (hself₂ : ∀ ω, ω ∈ c₂ ω) (hpart₂ : ∀ ω ω', ω' ∈ c₂ ω → c₂ ω' = c₂ ω)
    (hpos₂ : ∀ ω, 0 < ∑ x ∈ c₂ ω, p x)
    (M : Finset Ω) (w : Ω) (hw : w ∈ M)
    (hM₁ : ∀ x ∈ M, c₁ x ⊆ M) (hM₂ : ∀ x ∈ M, c₂ x ⊆ M)
    (q₁ q₂ : ℝ)
    (hq₁ : ∀ x ∈ M, posterior p E c₁ x = q₁)
    (hq₂ : ∀ x ∈ M, posterior p E c₂ x = q₂) :
    q₁ = q₂ := by
  have h1 : ∑ y ∈ M ∩ E, p y = q₁ * ∑ y ∈ M, p y :=
    sum_inter_eq_of_posterior_const p E c₁ hself₁ hpart₁ hpos₁ q₁ M.card M le_rfl hM₁ hq₁
  have h2 : ∑ y ∈ M ∩ E, p y = q₂ * ∑ y ∈ M, p y :=
    sum_inter_eq_of_posterior_const p E c₂ hself₂ hpart₂ hpos₂ q₂ M.card M le_rfl hM₂ hq₂
  have hMpos : 0 < ∑ y ∈ M, p y := by
    refine lt_of_lt_of_le (hpos₁ w) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (hM₁ w hw) (fun i _ _ => hp0 i)
  have := h1.symm.trans h2
  exact mul_right_cancel₀ (ne_of_gt hMpos) this

/-- Sanity check that the hypotheses of `aumann_agreement` are non-vacuous: the uniform
prior on `Bool × Bool`, agent 1 observing the first coordinate, agent 2 the second, and
`E` the diagonal event.  Both posteriors are constantly `1/2` on the whole space. -/
example :
    ∃ (p : Bool × Bool → ℝ) (E : Finset (Bool × Bool)) (c₁ c₂ : Bool × Bool → Finset (Bool × Bool))
      (M : Finset (Bool × Bool)),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω = 1) ∧ (∀ ω, ω ∈ c₁ ω) ∧ (∀ ω, ω ∈ c₂ ω) ∧
      (∀ ω, 0 < ∑ x ∈ c₁ ω, p x) ∧ (∀ ω, 0 < ∑ x ∈ c₂ ω, p x) ∧
      M.Nonempty ∧ (∀ x ∈ M, c₁ x ⊆ M) ∧ (∀ x ∈ M, c₂ x ⊆ M) ∧
      (∀ x ∈ M, posterior p E c₁ x = 1 / 2) ∧ (∀ x ∈ M, posterior p E c₂ x = 1 / 2) := by
  refine ⟨fun _ => 1 / 4, {(true, true), (false, false)},
    fun ω => {(ω.1, true), (ω.1, false)}, fun ω => {(true, ω.2), (false, ω.2)},
    Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_, ⟨(true, true), Finset.mem_univ _⟩,
    fun x _ => Finset.subset_univ _, fun x _ => Finset.subset_univ _, ?_, ?_⟩
  · intro ω; norm_num
  · norm_num [Fintype.sum_prod_type]
  · rintro ⟨a, b⟩; cases b <;> simp
  · rintro ⟨a, b⟩; cases a <;> simp
  · rintro ⟨a, b⟩; norm_num [Finset.sum_insert, Finset.sum_pair]
  · rintro ⟨a, b⟩; norm_num [Finset.sum_pair]
  · rintro ⟨a, b⟩ _; cases a <;> cases b <;>
      norm_num [posterior, Finset.sum_pair, Finset.insert_inter_distrib]
  · rintro ⟨a, b⟩ _; cases a <;> cases b <;>
      norm_num [posterior, Finset.sum_pair, Finset.insert_inter_distrib]

end Frontier

