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

/-- The prior probability of a (finite) event `S`, computed from the point masses `p`. -/
def prob (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, p ω

/-- An *information partition* of the state space, described by the map sending a state `ω`
to the cell `I ω` of states that the agent cannot distinguish from `ω`.  The two conditions
say that `ω` lies in its own cell and that the cells of two indistinguishable states agree,
i.e. that the cells form a partition of the state space. -/
def IsInfoPartition (I : Ω → Finset Ω) : Prop :=
  (∀ ω, ω ∈ I ω) ∧ ∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω

/-- An event `M` is *common knowledge* (between the two agents with information partitions
`I₁` and `I₂`) at every one of its states when it is a union of cells of each agent: from any
state of `M`, neither agent considers a state outside `M` possible, and this reasoning iterates
to all orders. -/
def IsCommonKnowledgeEvent (I₁ I₂ : Ω → Finset Ω) (M : Finset Ω) : Prop :=
  ∀ ω ∈ M, I₁ ω ⊆ M ∧ I₂ ω ⊆ M

section Partition

variable {I : Ω → Finset Ω} {M : Finset Ω}

/-- Inside a union `M` of cells, the fibre of the cell map over a cell `C` is exactly `C`. -/
theorem filter_cell_eq (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M)
    {C : Finset Ω} (hC : C ∈ M.image I) :
    {ω ∈ M | I ω = C} = C := by
  obtain ⟨ω₀, hω₀M, hω₀⟩ := Finset.mem_image.mp hC
  ext ω
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, hIω⟩
    exact hIω ▸ hI.1 ω
  · intro hωC
    have hωI : ω ∈ I ω₀ := hω₀ ▸ hωC
    refine ⟨hM ω₀ hω₀M hωI, ?_⟩
    rw [hI.2 ω₀ ω hωI, hω₀]

/-- Summing a function over the cells of a union `M` of cells recovers the sum over `M`. -/
theorem sum_over_cells (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M) (f : Ω → ℝ) :
    ∑ C ∈ M.image I, ∑ ω ∈ C, f ω = ∑ ω ∈ M, f ω := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := M.image I) (g := I)
    (fun ω hω => Finset.mem_image_of_mem I hω) f]
  exact Finset.sum_congr rfl fun C hC => by rw [filter_cell_eq hI hM hC]

/-- The prior mass of a union `M` of cells is the sum of the masses of its cells. -/
theorem prob_eq_sum_cells (p : Ω → ℝ) (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M) :
    ∑ C ∈ M.image I, prob p C = prob p M :=
  sum_over_cells hI hM p

/-- The prior mass of `E ∩ M`, for `M` a union of cells, is the sum of the masses of the
`E ∩ C` for `C` a cell. -/
theorem prob_inter_eq_sum_cells (p : Ω → ℝ) (E : Finset Ω) (hI : IsInfoPartition I)
    (hM : ∀ ω ∈ M, I ω ⊆ M) :
    ∑ C ∈ M.image I, prob p (E ∩ C) = prob p (E ∩ M) := by
  have key : ∀ S : Finset Ω, prob p (E ∩ S) = ∑ ω ∈ S, (if ω ∈ E then p ω else 0) := by
    intro S
    rw [Finset.inter_comm, prob, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  simp only [key]
  exact sum_over_cells hI hM _

/-- **Key computation.** If, throughout a union `M` of cells, an agent's conditional
probability of `E` given their cell equals `q`, then the unconditional probability of `E`
given `M` also equals `q` (in the product form `prob p (E ∩ M) = q * prob p M`). -/
theorem prob_inter_eq_of_posterior_const {p : Ω → ℝ} {E : Finset Ω} {q : ℝ}
    (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M)
    (hpost : ∀ ω ∈ M, 0 < prob p (I ω) ∧ prob p (E ∩ I ω) / prob p (I ω) = q) :
    prob p (E ∩ M) = q * prob p M := by
  rw [← prob_inter_eq_sum_cells p E hI hM, ← prob_eq_sum_cells p hI hM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨ω₀, hω₀M, hω₀⟩ := Finset.mem_image.mp hC
  obtain ⟨hpos, heq⟩ := hpost ω₀ hω₀M
  rw [hω₀] at hpos heq
  field_simp at heq
  linarith [heq]

end Partition

/-- **Aumann's agreement theorem** (finite common-prior version): two agents with a common
prior `p` and information partitions `I₁`, `I₂` cannot agree to disagree.  If it is common
knowledge (on the event `M`, which contains the actual state `ω₀`) that agent 1 assigns
posterior probability `q₁` to the event `E` and agent 2 assigns posterior probability `q₂`,
then `q₁ = q₂`.

The hypothesis `hp1` (that the prior is normalised) is included because a common prior is a
probability distribution; the argument itself only uses non-negativity together with the fact
that the cells occurring in `M` have positive prior mass. -/
theorem aumann_agreement {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (I₁ I₂ : Ω → Finset Ω) (hI₁ : IsInfoPartition I₁) (hI₂ : IsInfoPartition I₂)
    (E M : Finset Ω) (ω₀ : Ω) (hω₀ : ω₀ ∈ M)
    (hCK : IsCommonKnowledgeEvent I₁ I₂ M)
    (q₁ q₂ : ℝ)
    (h₁ : ∀ ω ∈ M, 0 < prob p (I₁ ω) ∧ prob p (E ∩ I₁ ω) / prob p (I₁ ω) = q₁)
    (h₂ : ∀ ω ∈ M, 0 < prob p (I₂ ω) ∧ prob p (E ∩ I₂ ω) / prob p (I₂ ω) = q₂) :
    q₁ = q₂ := by
  have hM₁ : ∀ ω ∈ M, I₁ ω ⊆ M := fun ω hω => (hCK ω hω).1
  have hM₂ : ∀ ω ∈ M, I₂ ω ⊆ M := fun ω hω => (hCK ω hω).2
  have e₁ : prob p (E ∩ M) = q₁ * prob p M :=
    prob_inter_eq_of_posterior_const hI₁ hM₁ h₁
  have e₂ : prob p (E ∩ M) = q₂ * prob p M :=
    prob_inter_eq_of_posterior_const hI₂ hM₂ h₂
  -- `M` has positive prior mass, since it contains the (positive-mass) cell `I₁ ω₀`.
  have hpos : 0 < prob p M := by
    have hsub : I₁ ω₀ ⊆ M := hM₁ ω₀ hω₀
    have : prob p (I₁ ω₀) ≤ prob p M :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hp0 ω
    exact lt_of_lt_of_le (h₁ ω₀ hω₀).1 this
  have := e₁.symm.trans e₂
  exact mul_right_cancel₀ (ne_of_gt hpos) this

/-- Restatement: the agents cannot *agree to disagree*. -/
theorem not_agree_to_disagree {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (I₁ I₂ : Ω → Finset Ω) (hI₁ : IsInfoPartition I₁) (hI₂ : IsInfoPartition I₂)
    (E M : Finset Ω) (ω₀ : Ω) (hω₀ : ω₀ ∈ M)
    (hCK : IsCommonKnowledgeEvent I₁ I₂ M)
    (q₁ q₂ : ℝ)
    (h₁ : ∀ ω ∈ M, 0 < prob p (I₁ ω) ∧ prob p (E ∩ I₁ ω) / prob p (I₁ ω) = q₁)
    (h₂ : ∀ ω ∈ M, 0 < prob p (I₂ ω) ∧ prob p (E ∩ I₂ ω) / prob p (I₂ ω) = q₂) :
    ¬ q₁ ≠ q₂ :=
  not_not_intro (aumann_agreement p hp0 hp1 I₁ I₂ hI₁ hI₂ E M ω₀ hω₀ hCK q₁ q₂ h₁ h₂)

/-! ### A concrete instance, showing the hypotheses above are satisfiable -/

section Example

open Finset

/-- Uniform common prior on four states. -/
noncomputable def exPrior : Fin 4 → ℝ := fun _ => 1/4

/-- Agent 1 learns whether the state is in `{0,1}` or in `{2,3}`. -/
def exI₁ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val < 2 then {0,1} else {2,3}

/-- Agent 2 learns the parity of the state. -/
def exI₂ : Fin 4 → Finset (Fin 4) := fun ω => if ω.val % 2 = 0 then {0,2} else {1,3}

/-- The event `{0,3}`; both agents assign it posterior probability `1/2` at every state. -/
def exE : Finset (Fin 4) := {0,3}

theorem exI₁_isInfoPartition : IsInfoPartition exI₁ := ⟨by decide, by decide⟩

theorem exI₂_isInfoPartition : IsInfoPartition exI₂ := ⟨by decide, by decide⟩

theorem exPosterior₁ : ∀ ω ∈ (univ : Finset (Fin 4)), 0 < prob exPrior (exI₁ ω) ∧
    prob exPrior (exE ∩ exI₁ ω) / prob exPrior (exI₁ ω) = 1/2 := by
  have c1 : (({0,3} : Finset (Fin 4)) ∩ {0,1}) = {0} := by decide
  have c2 : (({0,3} : Finset (Fin 4)) ∩ {2,3}) = {3} := by decide
  have d1 : (#({0,1} : Finset (Fin 4))) = 2 := by decide
  have d2 : (#({2,3} : Finset (Fin 4))) = 2 := by decide
  intro ω _
  fin_cases ω <;> norm_num [prob, exPrior, exI₁, exE, c1, c2, d1, d2]

theorem exPosterior₂ : ∀ ω ∈ (univ : Finset (Fin 4)), 0 < prob exPrior (exI₂ ω) ∧
    prob exPrior (exE ∩ exI₂ ω) / prob exPrior (exI₂ ω) = 1/2 := by
  have c1 : (({0,3} : Finset (Fin 4)) ∩ {0,2}) = {0} := by decide
  have c2 : (({0,3} : Finset (Fin 4)) ∩ {1,3}) = {3} := by decide
  have d1 : (#({0,2} : Finset (Fin 4))) = 2 := by decide
  have d2 : (#({1,3} : Finset (Fin 4))) = 2 := by decide
  intro ω _
  fin_cases ω <;> norm_num [prob, exPrior, exI₂, exE, c1, c2, d1, d2]

/-- The hypotheses of `Frontier.aumann_agreement` are jointly satisfiable: applying the theorem
to the two agents above (with the whole state space as the common-knowledge event) is legitimate,
and indeed both posteriors equal `1/2`. -/
theorem aumann_agreement_example : (1 : ℝ)/2 = 1/2 :=
  aumann_agreement exPrior (fun _ => by norm_num [exPrior])
    (by norm_num [exPrior]) exI₁ exI₂ exI₁_isInfoPartition exI₂_isInfoPartition
    exE univ 0 (mem_univ 0) (fun ω _ => ⟨subset_univ _, subset_univ _⟩)
    (1/2) (1/2) exPosterior₁ exPosterior₂

end Example

end Frontier

#print axioms Frontier.aumann_agreement
#print axioms Frontier.not_agree_to_disagree

