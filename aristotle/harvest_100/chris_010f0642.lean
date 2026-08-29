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

variable {Ω : Type*} [DecidableEq Ω]

/-- The probability of the (finite) event `S` under the weight function `p`. -/
def prob (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, p ω

omit [DecidableEq Ω] in
@[simp] lemma prob_empty (p : Ω → ℝ) : prob p (∅ : Finset Ω) = 0 := by
  simp [prob]

omit [DecidableEq Ω] in
lemma prob_pos_of_pos {p : Ω → ℝ} (hp : ∀ ω, 0 < p ω) {S : Finset Ω} (hS : S.Nonempty) :
    0 < prob p S :=
  Finset.sum_pos (fun ω _ => hp ω) hS

/-- An *information partition* of the state space: `I ω` is the set of states that the agent
cannot distinguish from `ω`.  The two axioms say that the cells `I ω` form a partition of `Ω`. -/
structure IsPartition (I : Ω → Finset Ω) : Prop where
  /-- Every state belongs to its own information cell. -/
  mem_self : ∀ ω, ω ∈ I ω
  /-- Two cells that meet are equal. -/
  eq_of_mem : ∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω

/-- An event `M` is *common knowledge at `ω₀`* for the two agents with information partitions
`I₁`, `I₂` when `ω₀ ∈ M` and `M` is self-evident to both agents, i.e. `M` is a union of cells
of `I₁` and also a union of cells of `I₂`.  (Equivalently, `M` is a cell of the meet of the two
partitions containing `ω₀`.) -/
structure IsCommonKnowledgeAt (I₁ I₂ : Ω → Finset Ω) (M : Finset Ω) (ω₀ : Ω) : Prop where
  /-- The current state lies in `M`. -/
  mem : ω₀ ∈ M
  /-- `M` is a union of cells of agent 1. -/
  closed₁ : ∀ ω ∈ M, I₁ ω ⊆ M
  /-- `M` is a union of cells of agent 2. -/
  closed₂ : ∀ ω ∈ M, I₂ ω ⊆ M

section Key

variable (p : Ω → ℝ) (I : Ω → Finset Ω) (E : Finset Ω) (q : ℝ)

/-- **Key aggregation lemma.**  If an event `M` is a union of cells of the partition `I`, and the
conditional probability of `E` given each such cell equals `q` (in multiplied form), then the
conditional probability of `E` given `M` equals `q` as well. -/
private lemma prob_inter_of_closed_aux (hI : IsPartition I) :
    ∀ (n : ℕ) (M : Finset Ω), M.card ≤ n → (∀ ω ∈ M, I ω ⊆ M) →
      (∀ ω ∈ M, prob p (E ∩ I ω) = q * prob p (I ω)) →
      prob p (E ∩ M) = q * prob p M := by
  intro n
  induction n with
  | zero =>
      intro M hcard _ _
      have : M = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst this
      simp
  | succ n ih =>
      intro M hcard hclosed hq
      rcases M.eq_empty_or_nonempty with rfl | ⟨ω, hω⟩
      · simp
      · set C : Finset Ω := I ω with hCdef
        have hCM : C ⊆ M := hclosed ω hω
        have hωC : ω ∈ C := hI.mem_self ω
        set M' : Finset Ω := M \ C with hM'def
        -- the complement `M'` is still a union of cells
        have hclosed' : ∀ ω' ∈ M', I ω' ⊆ M' := by
          intro ω' hω' x hx
          have hω'M : ω' ∈ M := (Finset.mem_sdiff.mp hω').1
          have hω'C : ω' ∉ C := (Finset.mem_sdiff.mp hω').2
          refine Finset.mem_sdiff.mpr ⟨hclosed ω' hω'M hx, ?_⟩
          intro hxC
          have h1 : I x = I ω' := hI.eq_of_mem ω' x hx
          have h2 : I x = C := hI.eq_of_mem ω x hxC
          have h3 : I ω' = C := by rw [← h1, h2]
          exact hω'C (h3 ▸ hI.mem_self ω')
        have hcard' : M'.card ≤ n := by
          have hlt : M'.card < M.card := by
            refine Finset.card_lt_card ?_
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro hsub
            exact (Finset.mem_sdiff.mp (hsub (hCM hωC))).2 hωC
          omega
        have hq' : ∀ ω' ∈ M', prob p (E ∩ I ω') = q * prob p (I ω') := by
          intro ω' hω'
          exact hq ω' (Finset.mem_sdiff.mp hω').1
        have hrec : prob p (E ∩ M') = q * prob p M' := ih M' hcard' hclosed' hq'
        -- split the probabilities along `M = C ⊔ M'`
        have hsplit : prob p M' + prob p C = prob p M := Finset.sum_sdiff hCM
        have hEsplit : prob p (E ∩ M') + prob p (E ∩ C) = prob p (E ∩ M) := by
          have hsub : E ∩ C ⊆ E ∩ M := Finset.inter_subset_inter_left hCM
          have hset : (E ∩ M) \ (E ∩ C) = E ∩ M' := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_inter, hM'def]
            tauto
          have := Finset.sum_sdiff (f := p) hsub
          rw [hset] at this
          exact this
        have hqC : prob p (E ∩ C) = q * prob p C := hq ω hω
        calc prob p (E ∩ M) = prob p (E ∩ M') + prob p (E ∩ C) := hEsplit.symm
          _ = q * prob p M' + q * prob p C := by rw [hrec, hqC]
          _ = q * (prob p M' + prob p C) := by ring
          _ = q * prob p M := by rw [hsplit]

lemma prob_inter_of_closed (hI : IsPartition I) (M : Finset Ω)
    (hclosed : ∀ ω ∈ M, I ω ⊆ M)
    (hq : ∀ ω ∈ M, prob p (E ∩ I ω) = q * prob p (I ω)) :
    prob p (E ∩ M) = q * prob p M :=
  prob_inter_of_closed_aux p I E q hI M.card M le_rfl hclosed hq

end Key

/-- **Aumann's agreement theorem** (finite state space, full-support common prior).

Two agents share a common prior `p` on a finite state space `Ω` and have information partitions
`I₁` and `I₂`.  At the state `ω₀` it is common knowledge (witnessed by the self-evident event `M`)
that agent 1's posterior probability of the event `E` is `q₁` and agent 2's posterior probability
of `E` is `q₂`.  Then `q₁ = q₂`: the agents cannot agree to disagree.

The hypothesis `hsum` (that the prior is normalised) is part of the statement that `p` is a common
prior, but it is not needed for the argument; only positivity of the prior is used. -/
theorem aumann_agreement [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω) (hsum : ∑ ω, p ω = 1)
    (I₁ I₂ : Ω → Finset Ω) (h₁ : IsPartition I₁) (h₂ : IsPartition I₂)
    (E M : Finset Ω) (ω₀ : Ω) (hck : IsCommonKnowledgeAt I₁ I₂ M ω₀)
    (q₁ q₂ : ℝ)
    (hq₁ : ∀ ω ∈ M, prob p (E ∩ I₁ ω) / prob p (I₁ ω) = q₁)
    (hq₂ : ∀ ω ∈ M, prob p (E ∩ I₂ ω) / prob p (I₂ ω) = q₂) :
    q₁ = q₂ := by
  have hMne : M.Nonempty := ⟨ω₀, hck.mem⟩
  have hMpos : 0 < prob p M := prob_pos_of_pos hp hMne
  -- turn the conditional-probability hypotheses into multiplicative form
  have hq₁' : ∀ ω ∈ M, prob p (E ∩ I₁ ω) = q₁ * prob p (I₁ ω) := by
    intro ω hω
    have hcell : prob p (I₁ ω) ≠ 0 := ne_of_gt (prob_pos_of_pos hp ⟨ω, h₁.mem_self ω⟩)
    rw [← hq₁ ω hω]
    field_simp
  have hq₂' : ∀ ω ∈ M, prob p (E ∩ I₂ ω) = q₂ * prob p (I₂ ω) := by
    intro ω hω
    have hcell : prob p (I₂ ω) ≠ 0 := ne_of_gt (prob_pos_of_pos hp ⟨ω, h₂.mem_self ω⟩)
    rw [← hq₂ ω hω]
    field_simp
  have e₁ : prob p (E ∩ M) = q₁ * prob p M :=
    prob_inter_of_closed p I₁ E q₁ h₁ M hck.closed₁ hq₁'
  have e₂ : prob p (E ∩ M) = q₂ * prob p M :=
    prob_inter_of_closed p I₂ E q₂ h₂ M hck.closed₂ hq₂'
  have : q₁ * prob p M = q₂ * prob p M := by rw [← e₁, ← e₂]
  exact mul_right_cancel₀ (ne_of_gt hMpos) this

/-! ### Non-vacuity check

The hypotheses of `Frontier.aumann_agreement` are satisfiable in a genuinely non-trivial
instance: four equally likely states, two *different* information partitions, and an event `E`
whose posterior is `1/2` for both agents in every state. -/

section Nonvacuity

/-- The uniform prior on four states. -/
noncomputable def unif : Fin 4 → ℝ := fun _ => 1 / 4

/-- Agent 1 learns whether the state lies in `{0,1}` or in `{2,3}`. -/
def K₁ : Fin 4 → Finset (Fin 4) := ![{0, 1}, {0, 1}, {2, 3}, {2, 3}]

/-- Agent 2 learns whether the state lies in `{3,0}` or in `{1,2}`. -/
def K₂ : Fin 4 → Finset (Fin 4) := ![{3, 0}, {1, 2}, {1, 2}, {3, 0}]

/-- The event under discussion. -/
def Ev : Finset (Fin 4) := {0, 2}

private lemma prob_unif (S : Finset (Fin 4)) : prob unif S = S.card / 4 := by
  simp [prob, unif, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma unif_post (S T : Finset (Fin 4)) (hT : 0 < T.card) :
    prob unif S / prob unif T = (S.card : ℝ) / (T.card : ℝ) := by
  have hne : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [prob_unif, prob_unif]
  field_simp

/-- All hypotheses of `Frontier.aumann_agreement` hold simultaneously in a non-degenerate
example with two distinct information partitions, so the theorem is not vacuous. -/
theorem aumann_hypotheses_satisfiable :
    (∀ ω, 0 < unif ω) ∧ (∑ ω, unif ω = 1) ∧
    IsPartition K₁ ∧ IsPartition K₂ ∧ K₁ ≠ K₂ ∧
    IsCommonKnowledgeAt K₁ K₂ Finset.univ 0 ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), prob unif (Ev ∩ K₁ ω) / prob unif (K₁ ω) = 1 / 2) ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), prob unif (Ev ∩ K₂ ω) / prob unif (K₂ ω) = 1 / 2) := by
  refine ⟨fun ω => by norm_num [unif], by norm_num [unif], ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide⟩, ?_, ?_⟩
  · have hcards : ∀ ω : Fin 4, (Ev ∩ K₁ ω).card = 1 ∧ (K₁ ω).card = 2 := by decide
    intro ω _
    obtain ⟨h1, h2⟩ := hcards ω
    rw [unif_post _ _ (by omega), h1, h2]
    norm_num
  · have hcards : ∀ ω : Fin 4, (Ev ∩ K₂ ω).card = 1 ∧ (K₂ ω).card = 2 := by decide
    intro ω _
    obtain ⟨h1, h2⟩ := hcards ω
    rw [unif_post _ _ (by omega), h1, h2]
    norm_num

end Nonvacuity

#print axioms Frontier.aumann_agreement
#print axioms Frontier.aumann_hypotheses_satisfiable

end Frontier

