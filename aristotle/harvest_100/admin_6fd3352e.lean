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

/-- The conditional probability of the event `E` given the (information) cell `C`,
computed from the weight function `p`. -/
noncomputable def condProb {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (E C : Finset Ω) : ℝ :=
  (∑ y ∈ C ∩ E, p y) / (∑ y ∈ C, p y)

/-- Key aggregation lemma: if a finite set `M` is closed under the information map `I`
(i.e. it is a union of cells of the partition induced by `I`), and every cell of a point of `M`
assigns the event `E` conditional probability `q` (in multiplicative form), then `M` itself
assigns `E` conditional probability `q` (in multiplicative form). -/
theorem sum_eq_of_closed {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (heq : ∀ x y, y ∈ I x → I y = I x)
    (E : Finset Ω) (q : ℝ) :
    ∀ M : Finset Ω, (∀ x ∈ M, I x ⊆ M) →
      (∀ x ∈ M, (∑ y ∈ I x ∩ E, p y) = q * ∑ y ∈ I x, p y) →
      (∑ y ∈ M ∩ E, p y) = q * ∑ y ∈ M, p y := by
  intro M
  induction M using Finset.strongInduction with
  | _ M ih =>
    intro hclosed hq
    rcases M.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hCM : I x ⊆ M := hclosed x hx
      have hxC : x ∈ I x := hself x
      have hsub : M \ I x ⊂ M := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨x, hx, ?_⟩
        simp [hxC]
      have hclosed' : ∀ y ∈ M \ I x, I y ⊆ M \ I x := by
        intro y hy z hz
        obtain ⟨hyM, hyC⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_sdiff.mpr ⟨hclosed y hyM hz, ?_⟩
        intro hzC
        have h1 : I z = I y := heq y z hz
        have h2 : I z = I x := heq x z hzC
        have h3 : I y = I x := h1.symm.trans h2
        exact hyC (h3 ▸ hself y)
      have hq' : ∀ y ∈ M \ I x, (∑ z ∈ I y ∩ E, p z) = q * ∑ z ∈ I y, p z :=
        fun y hy => hq y (Finset.mem_sdiff.mp hy).1
      have IH := ih (M \ I x) hsub hclosed' hq'
      have hsplitE : M ∩ E = (I x ∩ E) ∪ ((M \ I x) ∩ E) := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨hzM, hzE⟩
          by_cases hzC : z ∈ I x
          · exact Or.inl ⟨hzC, hzE⟩
          · exact Or.inr ⟨⟨hzM, hzC⟩, hzE⟩
        · rintro (⟨hzC, hzE⟩ | ⟨⟨hzM, _⟩, hzE⟩)
          · exact ⟨hCM hzC, hzE⟩
          · exact ⟨hzM, hzE⟩
      have hdisjE : Disjoint (I x ∩ E) ((M \ I x) ∩ E) := by
        refine Finset.disjoint_left.2 ?_
        intro z hz hz'
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz').1).2 (Finset.mem_inter.mp hz).1
      have hsplit : M = I x ∪ (M \ I x) := (Finset.union_sdiff_of_subset hCM).symm
      have hdisj : Disjoint (I x) (M \ I x) := Finset.disjoint_sdiff
      rw [hsplitE, Finset.sum_union hdisjE, IH, hq x hx]
      conv_rhs => rw [hsplit]
      rw [Finset.sum_union hdisj]
      ring

/-- **Aumann's agreement theorem** (finite, base case).

Two agents share a common prior `p` (a nonnegative weight function on a state space `Ω`)
and have information partitions given by the cell maps `I₁`, `I₂` (each point lies in its own
cell, and cells of points in a common cell coincide).  `M` is a common-knowledge component at the
actual state `w`: it contains `w` and is closed under both information maps.  If, throughout `M`,
agent 1's posterior for the event `E` is `q₁` and agent 2's posterior is `q₂` — i.e. the posteriors
are common knowledge at `w` — then `q₁ = q₂`: the agents cannot agree to disagree.

(Normalization `∑ x, p x = 1` of the prior is not needed for the argument, so it is not assumed.) -/
theorem aumann_agreement {Ω : Type*} [DecidableEq Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (I₁ I₂ : Ω → Finset Ω)
    (h1self : ∀ x, x ∈ I₁ x) (h1eq : ∀ x y, y ∈ I₁ x → I₁ y = I₁ x)
    (h2self : ∀ x, x ∈ I₂ x) (h2eq : ∀ x y, y ∈ I₂ x → I₂ y = I₂ x)
    (E M : Finset Ω) (w : Ω) (hw : w ∈ M)
    (hM1 : ∀ x ∈ M, I₁ x ⊆ M) (hM2 : ∀ x ∈ M, I₂ x ⊆ M)
    (hpos1 : ∀ x ∈ M, 0 < ∑ y ∈ I₁ x, p y) (hpos2 : ∀ x ∈ M, 0 < ∑ y ∈ I₂ x, p y)
    (q₁ q₂ : ℝ)
    (hq1 : ∀ x ∈ M, condProb p E (I₁ x) = q₁)
    (hq2 : ∀ x ∈ M, condProb p E (I₂ x) = q₂) :
    q₁ = q₂ := by
  have hmul1 : ∀ x ∈ M, (∑ y ∈ I₁ x ∩ E, p y) = q₁ * ∑ y ∈ I₁ x, p y := by
    intro x hx
    have := hq1 x hx
    rw [condProb, div_eq_iff (ne_of_gt (hpos1 x hx))] at this
    rw [this, mul_comm]
  have hmul2 : ∀ x ∈ M, (∑ y ∈ I₂ x ∩ E, p y) = q₂ * ∑ y ∈ I₂ x, p y := by
    intro x hx
    have := hq2 x hx
    rw [condProb, div_eq_iff (ne_of_gt (hpos2 x hx))] at this
    rw [this, mul_comm]
  have e1 : (∑ y ∈ M ∩ E, p y) = q₁ * ∑ y ∈ M, p y :=
    sum_eq_of_closed p I₁ h1self h1eq E q₁ M hM1 hmul1
  have e2 : (∑ y ∈ M ∩ E, p y) = q₂ * ∑ y ∈ M, p y :=
    sum_eq_of_closed p I₂ h2self h2eq E q₂ M hM2 hmul2
  have hMpos : 0 < ∑ y ∈ M, p y := by
    refine lt_of_lt_of_le (hpos1 w hw) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (hM1 w hw) (fun i _ _ => hp i)
  have := e1.symm.trans e2
  exact mul_right_cancel₀ (ne_of_gt hMpos) this

/-! ### A concrete instance, witnessing that the hypotheses above are satisfiable -/

/-- Agent 1's information cells on a four-state space: `{0,1}` and `{2,3}`. -/
def exI₁ : Fin 4 → Finset (Fin 4) := ![{0, 1}, {0, 1}, {2, 3}, {2, 3}]

/-- Agent 2's information cells on a four-state space: `{0,3}` and `{1,2}`. -/
def exI₂ : Fin 4 → Finset (Fin 4) := ![{0, 3}, {1, 2}, {1, 2}, {0, 3}]

/-- The uniform prior on the four-state space. -/
noncomputable def exPrior : Fin 4 → ℝ := fun _ => 1 / 4

private theorem exPair_condProb {a b c : Fin 4} {E : Finset (Fin 4)} (hab : a ≠ b)
    (h : ({a, b} : Finset (Fin 4)) ∩ E = {c}) :
    condProb exPrior E {a, b} = 1 / 2 := by
  rw [condProb, h, Finset.sum_singleton, Finset.sum_pair hab]
  simp only [exPrior]
  norm_num

private theorem exPair_sum_pos {a b : Fin 4} (hab : a ≠ b) :
    0 < ∑ y ∈ ({a, b} : Finset (Fin 4)), exPrior y := by
  rw [Finset.sum_pair hab]
  simp only [exPrior]
  norm_num

/-- The hypotheses of `Frontier.aumann_agreement` are satisfiable in a nontrivial situation:
two agents with genuinely different (and incomparable) information partitions on a four-state
space, whose common-knowledge component is the whole space, both assign probability `1/2`
to the event `{0, 2}`. -/
theorem aumann_agreement_example :
    (∀ x, x ∈ exI₁ x) ∧ (∀ x y, y ∈ exI₁ x → exI₁ y = exI₁ x) ∧
    (∀ x, x ∈ exI₂ x) ∧ (∀ x y, y ∈ exI₂ x → exI₂ y = exI₂ x) ∧
    exI₁ 0 ≠ exI₂ 0 ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)), 0 < ∑ y ∈ exI₁ x, exPrior y) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)), 0 < ∑ y ∈ exI₂ x, exPrior y) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)),
      condProb exPrior ({0, 2} : Finset (Fin 4)) (exI₁ x) = 1 / 2) ∧
    (∀ x ∈ (Finset.univ : Finset (Fin 4)),
      condProb exPrior ({0, 2} : Finset (Fin 4)) (exI₂ x) = 1 / 2) := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have e1 : ({0, 1} ∩ {0, 2} : Finset (Fin 4)) = {0} := by decide
  have e2 : ({2, 3} ∩ {0, 2} : Finset (Fin 4)) = {2} := by decide
  have e3 : ({0, 3} ∩ {0, 2} : Finset (Fin 4)) = {0} := by decide
  have e4 : ({1, 2} ∩ {0, 2} : Finset (Fin 4)) = {2} := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro x _
    fin_cases x
    · exact exPair_sum_pos h01
    · exact exPair_sum_pos h01
    · exact exPair_sum_pos h23
    · exact exPair_sum_pos h23
  · intro x _
    fin_cases x
    · exact exPair_sum_pos h03
    · exact exPair_sum_pos h12
    · exact exPair_sum_pos h12
    · exact exPair_sum_pos h03
  · intro x _
    fin_cases x
    · exact exPair_condProb h01 e1
    · exact exPair_condProb h01 e1
    · exact exPair_condProb h23 e2
    · exact exPair_condProb h23 e2
  · intro x _
    fin_cases x
    · exact exPair_condProb h03 e3
    · exact exPair_condProb h12 e4
    · exact exPair_condProb h12 e4
    · exact exPair_condProb h03 e3

end Frontier

