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
noncomputable def posterior {Ω : Type*} [DecidableEq Ω]
    (p : Ω → ℝ) (E : Finset Ω) (cell : Ω → Finset Ω) (ω : Ω) : ℝ :=
  (∑ y ∈ cell ω ∩ E, p y) / (∑ y ∈ cell ω, p y)

/-- If an event `M` is a union of cells of the partition `cell`, and the posterior of
`E` is constantly `q` on `M`, then `p (E ∩ M) = q * p M`. -/
theorem sum_inter_eq_of_posterior_const {Ω : Type*} [DecidableEq Ω]
    (p : Ω → ℝ) (E : Finset Ω) (cell : Ω → Finset Ω)
    (hself : ∀ ω, ω ∈ cell ω)
    (hpart : ∀ ω ω', ω' ∈ cell ω → cell ω' = cell ω)
    (hpos : ∀ ω, 0 < ∑ x ∈ cell ω, p x)
    (q : ℝ) :
    ∀ (n : ℕ) (M : Finset Ω), M.card ≤ n → (∀ x ∈ M, cell x ⊆ M) →
      (∀ x ∈ M, posterior p E cell x = q) →
      ∑ y ∈ M ∩ E, p y = q * ∑ y ∈ M, p y := by
  intro n
  induction n with
  | zero =>
      intro M hcard _ _
      have hM : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hM
      simp
  | succ n ih =>
      intro M hcard hM hq
      rcases M.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
      · simp
      · have hCM : cell w ⊆ M := hM w hw
        have hdisj : ∀ x ∈ M \ cell w, Disjoint (cell x) (cell w) := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.disjoint_left]
          intro y hy hy'
          have h1 : cell y = cell x := hpart x y hy
          have h2 : cell y = cell w := hpart w y hy'
          have h3 : cell x = cell w := h1 ▸ h2
          exact hx.2 (h3 ▸ hself x)
        have hM'sub : ∀ x ∈ M \ cell w, cell x ⊆ M \ cell w := by
          intro x hx y hy
          rw [Finset.mem_sdiff] at hx ⊢
          refine ⟨hM x hx.1 hy, ?_⟩
          intro hy'
          exact (Finset.disjoint_left.mp (hdisj x (Finset.mem_sdiff.mpr hx)) hy) hy'
        have hcard' : (M \ cell w).card ≤ n := by
          have hss : M \ cell w ⊂ M := by
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro hsub
            have := hsub hw
            rw [Finset.mem_sdiff] at this
            exact this.2 (hself w)
          have := Finset.card_lt_card hss
          omega
        have hq' : ∀ x ∈ M \ cell w, posterior p E cell x = q := fun x hx =>
          hq x (Finset.mem_sdiff.mp hx).1
        have IH := ih (M \ cell w) hcard' hM'sub hq'
        -- the cell of `w` contributes `q * p (cell w)`
        have hcellw : ∑ y ∈ cell w ∩ E, p y = q * ∑ y ∈ cell w, p y := by
          have h := hq w hw
          rw [posterior, div_eq_iff (ne_of_gt (hpos w))] at h
          rw [h, mul_comm]
        -- split the sums
        have hsplit1 : ∑ y ∈ M \ cell w, p y + ∑ y ∈ cell w, p y = ∑ y ∈ M, p y :=
          Finset.sum_sdiff hCM
        have hEsub : cell w ∩ E ⊆ M ∩ E := by
          intro x hx
          rw [Finset.mem_inter] at hx ⊢
          exact ⟨hCM hx.1, hx.2⟩
        have hsdiff : (M ∩ E) \ (cell w ∩ E) = (M \ cell w) ∩ E := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_inter]
          tauto
        have hsplit2 : ∑ y ∈ (M \ cell w) ∩ E, p y + ∑ y ∈ cell w ∩ E, p y
            = ∑ y ∈ M ∩ E, p y := by
          rw [← hsdiff]
          exact Finset.sum_sdiff hEsub
        rw [← hsplit2, IH, hcellw, ← hsplit1]
        ring

/-- **Aumann's agreement theorem** (finite state space, base case).

`p` is a common prior on a finite state space `Ω`, and the two agents have information
partitions given by their cell maps `c₁` and `c₂` (each state lies in its own cell,
cells of a partition coincide or are disjoint, and every cell has positive prior
probability).  If at some state the fact that agent 1's posterior of `E` is `q₁` and
agent 2's posterior of `E` is `q₂` is common knowledge — formalized by a nonempty
event `M` closed under both agents' cells on which the two posteriors are constantly
`q₁` and `q₂` — then `q₁ = q₂`: the agents cannot agree to disagree.

The hypothesis `hp1` (that the prior is normalized) is part of the statement that `p`
is a prior; it is kept for faithfulness even though the argument does not use it. -/
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

